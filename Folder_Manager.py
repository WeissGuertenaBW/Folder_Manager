#!/usr/bin/env python3
# APP VERSION: Folder Manager v1.0.54

"""Folder Manager application shell.

Media preview, auxiliary-window, debugger, and scanner behavior lives in the
shared ``shared_media_tools`` module used by both Folder Manager and Delta
Downloader.  The code below is intentionally limited to Folder Manager's file
browser and application wiring.
"""

from __future__ import annotations

import concurrent.futures
import os
import re
import shutil
import sys
import threading
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple


def _load_shared_media_tools():
    programs_root = Path(__file__).resolve().parents[2]
    organized_shared_root = programs_root / "Z_Shared_Tools"
    if (
        (organized_shared_root / "shared_media_tools.py").is_file()
        and str(organized_shared_root) not in sys.path
    ):
        sys.path.insert(0, str(organized_shared_root))
    try:
        import shared_media_tools as module
        return module
    except ModuleNotFoundError as exc:
        if exc.name != "shared_media_tools":
            raise
        if str(programs_root) not in sys.path:
            sys.path.insert(0, str(programs_root))
        import shared_media_tools as module
        return module


_shared_media_tools = _load_shared_media_tools()
_shared_media_tools.configure_shared_runtime(
    settings_org="FolderManager",
    settings_app="Folder Manager",
    debug_window_title="Folder Manager Debug",
    diagnostic_folder="Folder Manager",
)

# Load the shared runtime before Qt imports: it configures the media backend.
from PySide6.QtCore import (
    QEvent,
    QFileSystemWatcher,
    QSize,
    QTimer,
    Qt,
)
from PySide6.QtGui import (
    QBrush,
    QColor,
    QDragEnterEvent,
    QDropEvent,
    QKeySequence,
    QShortcut,
)
from PySide6.QtWidgets import (
    QAbstractItemView,
    QApplication,
    QFileDialog,
    QHBoxLayout,
    QHeaderView,
    QLabel,
    QMainWindow,
    QMenu,
    QMessageBox,
    QProgressBar,
    QPushButton,
    QSizePolicy,
    QSplitter,
    QToolButton,
    QTreeWidgetItem,
    QVBoxLayout,
    QWidget,
)
from shared_media_tools import (
    APP_DISPLAY_TITLE,
    APP_VERSION,
    BadFileDialog,
    BrowserAction,
    DateRangeCard,
    DetailRow,
    DuplicateDialog,
    FOLDER_PROGRESS_ROLE,
    FileInfo,
    FileOperationMove,
    FileTreeWidget,
    FolderMetricSignals,
    FolderProgressDelegate,
    FolderSummary,
    LargePreviewDialog,
    MediaMeta,
    MetricCard,
    PreviewPanel,
    RenameWorker,
    StatisticsCard,
    TrashMove,
    TrashMoveWorker,
    WINDOW_TRACE_BUILD_ID,
    capture_standard_window_geometry,
    compact_date_range_text,
    configure_settled_window_geometry,
    connect_tree_header_persistence,
    date_text,
    debug_log,
    debug_window_close_context,
    direct_entry_signature,
    drain_preview_workers,
    drain_scan_workers,
    file_info,
    file_size_histogram,
    file_size_stats_text,
    folder_display_name,
    folder_info,
    human_count,
    human_size,
    is_ignored_fs_entry,
    is_video_path,
    kind_for_path,
    list_child_folders,
    list_files,
    load_previous_watchdog_diagnostics,
    move_to_trash_recorded,
    natural_path_key,
    natural_text_key,
    open_file_reusing_finder,
    open_folder_in_finder,
    promote_macos_zoom_to_fullscreen,
    recursive_folder_info,
    recursive_folder_infos,
    restore_tree_header_state,
    retire_thread_worker,
    reveal_in_finder,
    save_window_geometry,
    scan_folder,
    schedule_macos_native_fullscreen_button,
    schedule_packaged_media_smoke,
    schedule_settled_window_geometry_remember,
    show_debug_window,
    sortable_creation_time,
    sortable_file_size,
    start_application_watchdog,
    stop_application_watchdog,
    strip_leading_indexes,
    strip_order_prefixes,
    track_standard_fullscreen_change,
    unique_path,
)


def __getattr__(name: str):
    """Keep legacy ``Folder_Manager.SharedHelper`` imports working on demand."""
    if name.startswith("__"):
        raise AttributeError(f"module {__name__!r} has no attribute {name!r}")
    return getattr(_shared_media_tools, name)


class DropBox(QLabel):
    def __init__(self, on_path_dropped, on_folder_clicked=None, on_empty_clicked=None):
        super().__init__("Drop a folder")
        self.on_path_dropped = on_path_dropped
        self.on_folder_clicked = on_folder_clicked
        self.on_empty_clicked = on_empty_clicked
        self.current_folder: Optional[Path] = None
        self.setAcceptDrops(True)
        self.setAlignment(Qt.AlignCenter)
        self.setMinimumHeight(82)
        self.setObjectName("DropBox")
        self.setCursor(Qt.PointingHandCursor)
        self.setToolTip("Click to open the current folder in Finder")

    def set_folder(self, folder: Optional[Path]):
        self.current_folder = folder
        if folder:
            self.setText(folder_display_name(folder.name))
            self.setToolTip("Click to open this folder in Finder")
        else:
            self.setText("Drop a folder")
            self.setToolTip("Click to choose a folder, or drop one here")

    def mousePressEvent(self, event):
        if event.button() == Qt.LeftButton:
            if self.current_folder and self.current_folder.exists():
                if self.on_folder_clicked:
                    self.on_folder_clicked(self.current_folder)
            elif self.on_empty_clicked:
                self.on_empty_clicked()
            event.accept()
            return
        super().mousePressEvent(event)

    def dragEnterEvent(self, event: QDragEnterEvent):
        if event.mimeData().hasUrls():
            for url in event.mimeData().urls():
                if url.isLocalFile():
                    event.acceptProposedAction()
                    return
        event.ignore()

    def dropEvent(self, event: QDropEvent):
        for url in event.mimeData().urls():
            if url.isLocalFile():
                path = Path(url.toLocalFile())
                self.on_path_dropped(path)
                event.acceptProposedAction()
                return
        event.ignore()


class BreadcrumbLabel(QLabel):
    def __init__(self, text: str, path: Path, on_clicked):
        super().__init__(text)
        self.path = path
        self.on_clicked = on_clicked
        self.setCursor(Qt.PointingHandCursor)
        self.setObjectName("BreadcrumbSegment")
        self.setToolTip(str(path))

    def mousePressEvent(self, event):
        if event.button() == Qt.LeftButton:
            self.on_clicked(self.path)
            event.accept()
            return
        super().mousePressEvent(event)


class BreadcrumbPath(QWidget):
    def __init__(self, on_folder_clicked):
        super().__init__()
        self.on_folder_clicked = on_folder_clicked
        self.current_folder: Optional[Path] = None
        self.layout = QHBoxLayout(self)
        self.layout.setContentsMargins(0, 0, 0, 0)
        self.layout.setSpacing(0)
        self.setObjectName("BreadcrumbPath")
        self.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)
        self.set_folder(None)

    def clear(self):
        while self.layout.count():
            item = self.layout.takeAt(0)
            widget = item.widget()
            if widget:
                widget.deleteLater()

    def set_folder(self, folder: Optional[Path]):
        self.current_folder = folder
        self.clear()
        if not folder:
            label = QLabel("No folder loaded")
            label.setObjectName("BreadcrumbMuted")
            self.layout.addWidget(label)
            self.layout.addStretch(1)
            return

        parts = list(folder.parts)
        path = Path(parts[0])
        for index, part in enumerate(parts):
            if index == 0:
                label_text = part
            else:
                path = path / part
                label_text = folder_display_name(part)

            segment = BreadcrumbLabel(label_text, path, self.on_folder_clicked)
            self.layout.addWidget(segment)
            if index < len(parts) - 1 and not (index == 0 and part == os.sep):
                slash = QLabel("/")
                slash.setObjectName("BreadcrumbSeparator")
                self.layout.addWidget(slash)
        self.layout.addStretch(1)


class FolderManager(QMainWindow):
    TABLE_HEADERS = ["Name", "Kind", "Ext", "Size", "Created", "Modified"]
    ROLE_KIND = Qt.UserRole
    ROLE_PATH = Qt.UserRole + 1
    ROLE_LOADED = Qt.UserRole + 2
    ROLE_GROUP_KEY = Qt.UserRole + 3

    def __init__(self):
        super().__init__()
        self.setWindowTitle(APP_DISPLAY_TITLE)
        self.resize(1220, 820)

        self._initialize_browser_state()
        self._initialize_folder_metrics()
        self._initialize_timers()

        root = QWidget()
        root.setObjectName("AppRoot")
        root.setAcceptDrops(True)
        self.setCentralWidget(root)
        self.setAcceptDrops(True)

        layout = QVBoxLayout(root)
        layout.setContentsMargins(14, 14, 14, 12)
        layout.setSpacing(10)

        self.build_header(layout)
        self.build_metrics(layout)
        self.build_actions(layout)
        self.build_body(layout)
        self.install_main_shortcuts()
        app = QApplication.instance()
        if app is not None:
            app.installEventFilter(self)

        self.status = QLabel("Ready")
        self.status.setObjectName("MutedLabel")
        layout.addWidget(self.status)

        self.update_empty_state()
        self.update_undo_button()
        self.restore_main_window_geometry()

    def _initialize_browser_state(self):
        """Selection, navigation, and file-operation state owned by the browser."""
        self.folder: Optional[Path] = None
        self.files: List[FileInfo] = []
        self.file_info_by_path: Dict[Path, FileInfo] = {}
        self.summary: Optional[FolderSummary] = None
        self.back_stack: List[Path] = []
        self.forward_stack: List[Path] = []
        self.undo_stack: List[BrowserAction] = []
        self.redo_stack: List[BrowserAction] = []
        self.duplicate_dialogs: List[DuplicateDialog] = []
        self.bad_file_dialogs: List[BadFileDialog] = []
        self.quicklook_dialog: Optional[LargePreviewDialog] = None
        self.last_preview_toggle_at = 0.0
        self.copy_path_feedback_active = False
        self.operation_worker: Optional[RenameWorker] = None
        self.trash_workers: List[TrashMoveWorker] = []
        self.pending_operation_created_dirs: List[Path] = []
        self.closing_after_operation_cancel = False
        self.closing_after_trash_moves = False
        self.closing_after_child_work = False
        self.browser_rename_suppress = False
        self.browser_rename_item: Optional[QTreeWidgetItem] = None
        self.browser_rename_path: Optional[Path] = None
        self.current_browser_active_path: Optional[Path] = None
        self.previous_browser_active_path: Optional[Path] = None
        self.debug_last_browser_selection_path: Optional[Path] = None
        self.sort_mode = "name"
        self.sort_reverse = False
        self.media_grouped = False
        self.current_folder_entry_signature: Tuple[Tuple[str, str], ...] = ()
        self.table_reloading = False
        self.pending_table_entries: List[Tuple[str, Path]] = []
        self.pending_table_total = 0
        self.pending_table_select_path: Optional[Path] = None
        self.pending_table_select_index: Optional[int] = None
        self.pending_table_open_state: set[str] = set()

    def _initialize_folder_metrics(self):
        """Calculate recursive folder sizes outside the UI thread."""
        self.folder_metric_cache: Dict[str, FileInfo] = {}
        self.folder_metric_futures: Dict[str, concurrent.futures.Future] = {}
        self.folder_metric_cancel = threading.Event()
        self.folder_metric_signals = FolderMetricSignals(self)
        self.folder_metric_signals.ready.connect(self.on_folder_metric_ready)
        self.folder_metric_executor = concurrent.futures.ThreadPoolExecutor(
            max_workers=max(2, min(4, (os.cpu_count() or 4) // 2)),
            thread_name_prefix="folder-manager-folders",
        )

    def _initialize_timers(self):
        """Coalesce UI work and keep the current directory in sync."""
        self.table_populate_timer = QTimer(self)
        self.table_populate_timer.timeout.connect(self.populate_table_chunk)
        self.selection_details_timer = QTimer(self)
        self.selection_details_timer.setSingleShot(True)
        self.selection_details_timer.timeout.connect(self.update_selection_details)
        self.pending_browser_preview_path: Optional[Path] = None
        self.browser_preview_timer = QTimer(self)
        self.browser_preview_timer.setSingleShot(True)
        self.browser_preview_timer.timeout.connect(self.apply_pending_browser_preview)
        # Expanding a large folder can make the visible-scope statistics expensive.
        # Debounce that work so the disclosure arrow responds immediately instead
        # of making the tree appear to shiver while the cards are recalculated.
        self.metrics_refresh_timer = QTimer(self)
        self.metrics_refresh_timer.setSingleShot(True)
        self.metrics_refresh_timer.timeout.connect(self.apply_metrics_refresh_for_current_view)
        self.folder_watcher = QFileSystemWatcher(self)
        self.folder_watcher.directoryChanged.connect(self.on_watched_folder_changed)
        self.reload_debounce = QTimer(self)
        self.reload_debounce.setSingleShot(True)
        self.reload_debounce.timeout.connect(self.reload_from_watcher)
        self.folder_reconcile_timer = QTimer(self)
        self.folder_reconcile_timer.setInterval(1200)
        self.folder_reconcile_timer.timeout.connect(self.reconcile_current_folder_entries)
        self.folder_reconcile_timer.start()

    def restore_main_window_geometry(self):
        """Restore the user's last window size and screen position."""
        configure_settled_window_geometry(self, "main", QSize(1220, 820))

    def save_main_window_geometry(self):
        """Persist the current window size and screen position."""
        save_window_geometry(self, "main")

    def eventFilter(self, obj, event):
        # A clicked histogram bucket temporarily replaces the summary line.
        # Any click outside the Statistics card restores the whole-distribution text.
        if event.type() == QEvent.MouseButtonPress and hasattr(self, "index_card"):
            try:
                if getattr(self.index_card.histogram, "selected_index", None) is not None:
                    widget = obj if isinstance(obj, QWidget) else None
                    inside_stats = False
                    while widget is not None:
                        if widget is self.index_card:
                            inside_stats = True
                            break
                        widget = widget.parentWidget()
                    if not inside_stats:
                        self.index_card.clear_selection()
            except Exception:
                pass
        return super().eventFilter(obj, event)

    def build_header(self, layout: QVBoxLayout):
        header = QHBoxLayout()
        header.setSpacing(12)
        layout.addLayout(header)

        self.back_btn = QPushButton("<")
        self.forward_btn = QPushButton(">")
        for nav_btn in (self.back_btn, self.forward_btn):
            nav_btn.setObjectName("NavButton")
            nav_btn.setFixedSize(34, 28)
            header.addWidget(nav_btn)

        title_box = QVBoxLayout()
        title_box.setSpacing(1)
        header.addLayout(title_box, stretch=1)

        title = QLabel(APP_DISPLAY_TITLE)
        title.setObjectName("AppTitle")
        self.path_label = BreadcrumbPath(self.navigate_to_breadcrumb)
        self.path_label.setObjectName("PathLabel")

        title_box.addWidget(title)
        title_box.addWidget(self.path_label)

        self.choose_btn = QPushButton("Choose Folder")
        self.choose_btn.setObjectName("BrightGreyButton")
        self.choose_btn.clicked.connect(self.choose_folder)
        self.copy_path_btn = QPushButton("Copy Path")
        self.copy_path_btn.setToolTip("Copy the current folder path")
        self.copy_path_btn.clicked.connect(self.copy_current_path)
        self.debug_btn = QPushButton("Debug")
        self.debug_btn.setToolTip("Open the live diagnostics and responsiveness monitor")
        self.debug_btn.clicked.connect(self.open_debug_dialog)
        header.addWidget(self.copy_path_btn)
        header.addWidget(self.debug_btn)
        header.addWidget(self.choose_btn)

        self.back_btn.clicked.connect(self.go_back)
        self.forward_btn.clicked.connect(self.go_forward)

        self.drop_box = DropBox(self.load_external_drop_path, open_folder_in_finder, self.choose_folder)
        layout.addWidget(self.drop_box)

    def open_debug_dialog(self):
        debug_log("window-trace", "diagnostic build", force=True, build=WINDOW_TRACE_BUILD_ID, version=APP_VERSION)
        window = show_debug_window(self)
        if window is None:
            return
        if not bool(window.property("folder_manager_button_hooked")):
            window.setProperty("folder_manager_button_hooked", True)
            def _refresh_after_debug_close(*_args):
                # ``destroyed`` can arrive while the main window's child widgets
                # are already being deleted. Queue the refresh and let the
                # guarded method decide whether anything is still alive.
                try:
                    QTimer.singleShot(0, self.update_auxiliary_window_buttons)
                except RuntimeError:
                    pass
            window.finished.connect(_refresh_after_debug_close)
            window.destroyed.connect(_refresh_after_debug_close)
        self.update_auxiliary_window_buttons()

    @staticmethod
    def window_is_visible(window) -> bool:
        if window is None:
            return False
        try:
            return window.isVisible()
        except RuntimeError:
            return False

    def update_auxiliary_window_buttons(self, folder_enabled: Optional[bool] = None):
        """Reflect auxiliary-window state without imposing window ordering.

        This method is also reached from ``finished``/``destroyed`` signals while
        the main window itself is being torn down.  At that point Python may
        still have attributes for buttons whose underlying C++ objects have
        already been deleted by Qt.  Treat those callbacks as harmless no-ops
        instead of letting Shiboken abort the diagnostic sequence.
        """
        try:
            if folder_enabled is None:
                folder_enabled = bool(self.folder and self.folder.exists())
            duplicate_open = any(self.window_is_visible(dialog) for dialog in self.duplicate_dialogs)
            bad_open = any(self.window_is_visible(dialog) for dialog in self.bad_file_dialogs)
            debug_open = self.window_is_visible(_shared_media_tools.DEBUG_WINDOW)
        except RuntimeError as exc:
            debug_log("window-trace", "auxiliary button refresh skipped during teardown", force=True,
                      error=f"{type(exc).__name__}: {exc}")
            return

        for attr, enabled in (
            ("dup_btn", bool(folder_enabled) and not duplicate_open),
            ("bad_scan_btn", bool(folder_enabled) and not bad_open),
            ("debug_btn", not debug_open),
        ):
            try:
                button = getattr(self, attr, None)
                if button is not None:
                    button.setEnabled(enabled)
            except RuntimeError as exc:
                # Python wrapper survived longer than the corresponding Qt
                # object. This is normal during shutdown/fullscreen teardown.
                debug_log("window-trace", "button already deleted during auxiliary refresh", force=True,
                          button=attr, error=f"{type(exc).__name__}: {exc}")

    def build_metrics(self, layout: QVBoxLayout):
        metrics = QHBoxLayout()
        metrics.setSpacing(8)
        layout.addLayout(metrics)

        self.file_card = MetricCard("Files", "#9b99cf")
        self.size_card = MetricCard("Total Size", "#9bb79f")
        self.size_card.set_clickable(True)
        self.size_card.set_meta_elide(True)
        self.size_card.setToolTip("Click to select the largest item. Double-click to reveal it in Finder.")
        self.type_card = MetricCard("Types", "#d4b27c")
        self.index_card = StatisticsCard("#8f98c8")
        self.range_card = DateRangeCard("#c98f8f")

        # Keep the summary cards fixed; let Types and Statistics share extra width.
        self.file_card.setFixedWidth(248)
        self.size_card.setFixedWidth(274)
        self.type_card.setMinimumWidth(248)
        self.type_card.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)
        self.type_card.meta.setMinimumWidth(0)
        self.type_card.meta.setSizePolicy(QSizePolicy.Ignored, QSizePolicy.Fixed)
        self.index_card.setMinimumWidth(293)
        self.range_card.setFixedWidth(270)
        self.size_card.clicked.connect(self.select_largest_item)
        self.size_card.doubleClicked.connect(self.reveal_largest_item)
        self.range_card.oldestClicked.connect(self.select_oldest_item)
        self.range_card.newestClicked.connect(self.select_newest_item)

        metrics.addWidget(self.file_card)
        metrics.addWidget(self.size_card)
        metrics.addWidget(self.type_card, stretch=1)
        metrics.addWidget(self.index_card, stretch=2)
        metrics.addWidget(self.range_card)

    def build_actions(self, layout: QVBoxLayout):
        actions = QHBoxLayout()
        actions.setSpacing(8)
        layout.addLayout(actions)

        self.reorder_btn = QPushButton("Reorder")
        self.order_created_btn = QPushButton("Order by Creation Date")
        self.order_size_btn = QPushButton("Order by Size")
        self.type_sort_btn = QPushButton("Group by Media Type")
        self.unorder_btn = QPushButton("Numberate")
        self.dup_btn = QPushButton("Duplicate Scan")
        self.bad_scan_btn = QPushButton("Bad File Scan")
        self.terminate_btn = QPushButton("Terminate")
        self.terminate_btn.setMinimumHeight(32)
        self.terminate_btn.setToolTip("Stop the current loading or file operation")
        self.terminate_btn.clicked.connect(self.terminate_current_action)
        self.undo_btn = QToolButton()
        self.undo_btn.setObjectName("UndoButton")
        self.undo_btn.setText("Undo")
        self.undo_btn.setToolButtonStyle(Qt.ToolButtonTextOnly)
        self.undo_btn.setFixedSize(72, 32)
        self.undo_btn.setToolTip("Undo last file operation (Command-Z)")
        self.undo_btn.clicked.connect(self.undo_browser_action)

        self.dup_btn.setObjectName("BrightGreyButton")
        self.bad_scan_btn.setObjectName("BrightGreyButton")
        self.terminate_btn.setObjectName("BrightGreyButton")

        buttons = [
            self.reorder_btn,
            self.order_created_btn,
            self.order_size_btn,
            self.type_sort_btn,
            self.unorder_btn,
            self.dup_btn,
            self.bad_scan_btn,
        ]

        for button in buttons:
            button.setMinimumHeight(32)
            actions.addWidget(button)

        # Keep task progress in the existing horizontal action strip so the main
        # window never grows/shrinks when a load or operation starts. The reserved
        # area lives only between Bad File Scan and Terminate.
        self.task_progress_container = QWidget()
        self.task_progress_container.setFixedHeight(32)
        self.task_progress_container.setMinimumWidth(260)
        self.task_progress_container.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)
        task_progress_layout = QHBoxLayout(self.task_progress_container)
        task_progress_layout.setContentsMargins(0, 0, 0, 0)
        task_progress_layout.setSpacing(8)
        # Progress lives here as a bar only. No text, so it cannot be clipped
        # between Bad File Scan and Terminate or make the row visually jitter.
        self.task_progress = QProgressBar()
        self.task_progress.setTextVisible(False)
        self.task_progress.setFixedWidth(240)
        self.task_progress.setFixedHeight(12)
        self.task_progress.setVisible(False)
        task_progress_layout.addStretch(1)
        task_progress_layout.addWidget(self.task_progress)
        actions.addWidget(self.task_progress_container, stretch=1)
        actions.addWidget(self.terminate_btn)
        actions.addWidget(self.undo_btn)

        self.reorder_btn.clicked.connect(self.reorder_to_folder_order)
        self.order_created_btn.clicked.connect(self.toggle_sort_by_creation_date)
        self.order_size_btn.clicked.connect(self.toggle_sort_by_size)
        self.unorder_btn.clicked.connect(self.toggle_numeration)
        self.type_sort_btn.clicked.connect(self.order_by_media_types)
        self.dup_btn.clicked.connect(self.open_duplicate_dialog)
        self.bad_scan_btn.clicked.connect(self.open_bad_file_dialog)


    def build_body(self, layout: QVBoxLayout):
        splitter = QSplitter(Qt.Horizontal)
        splitter.setObjectName("MainSplitter")
        layout.addWidget(splitter, stretch=1)
        splitter.addWidget(self._build_browser_table())
        splitter.addWidget(self._build_inspector())
        splitter.setChildrenCollapsible(False)
        splitter.setSizes([850, 370])
        # The inspector width is fixed; old saved splitter sizes must not override it.

    def _build_browser_table(self) -> FileTreeWidget:
        self.table = FileTreeWidget()
        self.table.return_renames = True
        self.table.setColumnCount(len(self.TABLE_HEADERS))
        self.table.setHeaderLabels(self.TABLE_HEADERS)
        self.table.setRootIsDecorated(False)
        self.table.setIndentation(22)
        self.table.setSelectionBehavior(QAbstractItemView.SelectRows)
        self.table.setSelectionMode(QAbstractItemView.ExtendedSelection)
        self.table.setEditTriggers(QAbstractItemView.NoEditTriggers)
        self.table.setAlternatingRowColors(True)
        self.table.setAllColumnsShowFocus(True)
        # Keep the viewport geometry constant while branches open and close.
        # Otherwise the vertical scrollbar can appear/disappear and nudge every
        # row sideways by a few pixels. Tree animation is disabled for the same
        # reason: disclosure should feel pinned, not rubbery.
        self.table.setVerticalScrollBarPolicy(Qt.ScrollBarAlwaysOn)
        self.table.setAnimated(False)
        self.table.setExpandsOnDoubleClick(False)
        self.table.header().setSectionsMovable(True)
        self.table.header().setStretchLastSection(True)
        self.table.header().setMinimumSectionSize(72)
        self.table.header().setSectionResizeMode(QHeaderView.Interactive)
        self.table.setColumnWidth(0, 360)
        self.table.setColumnWidth(1, 130)
        self.table.setColumnWidth(2, 80)
        self.table.setColumnWidth(3, 105)
        self.table.setColumnWidth(4, 180)
        self.table.setColumnWidth(5, 180)
        self.folder_progress_delegate = FolderProgressDelegate(self.table)
        self.table.setItemDelegate(self.folder_progress_delegate)
        self.table.itemDelegate().closeEditor.connect(self.on_browser_rename_editor_closed)
        self.table.setFolderDropEnabled(True)
        self.table.setFileDragEnabled(True)
        restore_tree_header_state(self.table, "main_v2")
        connect_tree_header_persistence(self.table, "main_v2")
        self.table.itemSelectionChanged.connect(self.schedule_selection_details_update)
        self.table.disclosurePressed.connect(self.toggle_browser_folder_header)

        # Expansion is intentionally only on the triangle/disclosure gutter.
        # Clicking a folder/header name selects it; double-clicking a real folder enters it.
        self.table.itemDoubleClicked.connect(self.on_browser_item_double_clicked)
        self.table.setContextMenuPolicy(Qt.CustomContextMenu)
        self.table.customContextMenuRequested.connect(self.open_browser_context_menu)
        self.table.deletePressed.connect(self.move_browser_selection_to_trash)
        self.table.undoPressed.connect(self.undo_browser_action)
        self.table.redoPressed.connect(self.redo_browser_action)
        self.table.openPressed.connect(self.open_browser_current_item)
        self.table.previewPressed.connect(self.preview_browser_current_item)
        self.table.reviewStepPressed.connect(self.preview_adjacent_browser_file)
        self.table.playPausePressed.connect(self.toggle_active_preview_playback)
        self.table.blankClicked.connect(self.clear_browser_selection)
        self.table.filesDropped.connect(self.drop_paths_into_current_folder)
        self.table.renamePressed.connect(self.rename_current_browser_item)
        self.table.itemChanged.connect(self.on_browser_item_changed)
        return self.table

    def _build_inspector(self) -> QWidget:
        inspector = QWidget()
        inspector.setObjectName("Inspector")
        # Keep the inspector/sidebar a fixed width so clicking different items
        # cannot make the file table or preview/details panel wiggle.
        inspector.setFixedWidth(370)
        inspector_layout = QVBoxLayout(inspector)
        inspector_layout.setContentsMargins(12, 12, 12, 12)
        inspector_layout.setSpacing(10)

        self.preview_panel = PreviewPanel("Select a file or folder to preview it here.", compact=True)
        self.preview_panel.zoomRequested.connect(self.zoom_browser_preview)
        self.preview_panel.metadataLoaded.connect(self.on_browser_preview_metadata_loaded)
        inspector_layout.addWidget(self.preview_panel)

        detail_title = QLabel("Selection")
        detail_title.setObjectName("SectionTitle")
        inspector_layout.addWidget(detail_title)

        self.detail_name = DetailRow("Name")
        self.detail_kind = DetailRow("Kind")
        self.detail_duration = DetailRow("Duration")
        self.detail_resolution = DetailRow("Resolution")
        self.detail_sample_rate = DetailRow("Sample Rate")
        self.detail_size = DetailRow("Size")
        self.detail_created = DetailRow("Created")
        self.detail_modified = DetailRow("Modified")
        self.detail_mime = DetailRow("MIME")
        self.detail_path = DetailRow("Path")
        self.detail_path.set_clickable(True)
        self.detail_path.clicked.connect(self.copy_selected_detail_path)

        self.detail_rows = (
            self.detail_name,
            self.detail_kind,
            self.detail_duration,
            self.detail_resolution,
            self.detail_sample_rate,
            self.detail_size,
            self.detail_created,
            self.detail_modified,
            self.detail_mime,
            self.detail_path,
        )
        for row in self.detail_rows:
            inspector_layout.addWidget(row)

        inspector_layout.addStretch(1)
        return inspector

    def install_main_shortcuts(self):
        self.undo_shortcut = QShortcut(QKeySequence.Undo, self)
        self.undo_shortcut.setContext(Qt.WindowShortcut)
        self.undo_shortcut.activated.connect(self.trigger_undo_shortcut)

        self.redo_shortcut = QShortcut(QKeySequence.Redo, self)
        self.redo_shortcut.setContext(Qt.WindowShortcut)
        self.redo_shortcut.activated.connect(self.redo_browser_action)

        self.preview_shortcut = QShortcut(QKeySequence(Qt.Key_Space), self)
        self.preview_shortcut.setContext(Qt.WindowShortcut)
        self.preview_shortcut.activated.connect(self.trigger_preview_shortcut)

    def trigger_undo_shortcut(self):
        if hasattr(self, "undo_btn") and self.undo_btn.isEnabled():
            self.undo_btn.setDown(True)
            QTimer.singleShot(120, lambda: self.undo_btn.setDown(False))
        self.undo_browser_action()

    def trigger_preview_shortcut(self):
        if self.browser_rename_item is not None:
            return
        if hasattr(self, "table") and self.table.state() == QAbstractItemView.EditingState:
            return
        self.preview_browser_current_item()

    def require_folder(self) -> Optional[Path]:
        if not self.folder or not self.folder.exists():
            QMessageBox.warning(self, "No folder", "Choose or drop a folder first.")
            return None
        return self.folder

    def choose_folder(self):
        desktop = Path.home() / "Desktop"
        start = str(desktop if desktop.exists() else Path.home())
        selected = QFileDialog.getExistingDirectory(self, "Choose Folder", start)
        if selected:
            self.load_folder(Path(selected))

    def copy_current_path(self):
        if not self.folder:
            return
        try:
            path_text = str(self.folder.expanduser().resolve())
        except OSError:
            path_text = str(self.folder.expanduser().absolute())
        QApplication.clipboard().setText(path_text)
        self.copy_path_feedback_active = True
        self.copy_path_btn.setText("Copied")
        self.copy_path_btn.setEnabled(False)
        self.status.setText("Copied full folder path")
        QTimer.singleShot(1000, self.reset_copy_path_button)

    def reset_copy_path_button(self):
        self.copy_path_feedback_active = False
        self.copy_path_btn.setText("Copy Path")
        self.copy_path_btn.setEnabled(bool(self.folder and self.folder.exists()))

    def copy_selected_detail_path(self):
        path = self.browser_item_path(self.table.currentItem()) if hasattr(self, "table") else None
        if not path:
            self.copy_current_path()
            return
        try:
            path_text = str(path.expanduser().resolve())
        except OSError:
            path_text = str(path.expanduser().absolute())
        QApplication.clipboard().setText(path_text)
        self.copy_path_feedback_active = True
        self.copy_path_btn.setText("Copied")
        self.copy_path_btn.setEnabled(False)
        self.status.setText("Copied selected path")
        QTimer.singleShot(1000, self.reset_copy_path_button)

    def load_folder(self, folder: Path):
        self.navigate_to_folder(folder, add_history=True)

    def load_external_drop_path(self, path: Path):
        self.load_external_drop_paths([path])

    def load_external_drop_paths(self, paths: List[Path]):
        if not paths:
            return
        target = paths[0].expanduser()
        if not target.exists():
            self.status.setText("Dropped item no longer exists")
            return
        if target.is_dir():
            self.navigate_to_folder(target, add_history=True)
            return
        parent = target.parent
        self.navigate_to_folder(parent, add_history=True)
        QTimer.singleShot(0, lambda path=target: self.select_path_in_browser_tree(path))

    def dragEnterEvent(self, event: QDragEnterEvent):
        if event.mimeData().hasUrls() and any(url.isLocalFile() for url in event.mimeData().urls()):
            event.acceptProposedAction()
            return
        event.ignore()

    def dragMoveEvent(self, event):
        if event.mimeData().hasUrls() and any(url.isLocalFile() for url in event.mimeData().urls()):
            event.acceptProposedAction()
            return
        event.ignore()

    def dropEvent(self, event: QDropEvent):
        paths = [Path(url.toLocalFile()) for url in event.mimeData().urls() if url.isLocalFile()]
        if paths:
            self.load_external_drop_paths(paths)
            event.acceptProposedAction()
            return
        event.ignore()

    def navigate_to_breadcrumb(self, folder: Path):
        if folder == self.folder:
            return
        self.navigate_to_folder(folder, add_history=True)

    def navigate_to_folder(self, folder: Path, add_history: bool = True):
        folder = folder.expanduser()
        if not folder.exists() or not folder.is_dir():
            QMessageBox.warning(self, "Missing folder", "That folder no longer exists.")
            return
        if add_history and self.folder and self.folder != folder:
            self.back_stack.append(self.folder)
            self.forward_stack.clear()
        self.folder = folder
        self.path_label.set_folder(folder)
        self.drop_box.set_folder(folder)
        self.update_folder_watcher(folder)
        self.reload_folder(f"Loaded {folder.name}")

    def update_folder_watcher(self, folder: Optional[Path]):
        watched = self.folder_watcher.directories()
        if watched:
            self.folder_watcher.removePaths(watched)
        if folder and folder.exists():
            self.folder_watcher.addPath(str(folder))

    def on_watched_folder_changed(self, _path: str):
        self.reload_debounce.start(1400 if self.has_active_trash_workers() else 350)

    def reconcile_current_folder_entries(self):
        folder = self.folder
        if not folder or not folder.exists():
            return
        folder_text = str(folder)
        if folder_text not in self.folder_watcher.directories():
            self.folder_watcher.addPath(folder_text)
        signature = direct_entry_signature(folder)
        if signature == self.current_folder_entry_signature:
            return
        self.current_folder_entry_signature = signature
        self.reload_debounce.start(350)

    def reload_from_watcher(self):
        if self.folder and self.folder.exists():
            if self.has_active_trash_workers():
                self.reload_debounce.start(1000)
                return
            selected = self.browser_item_path(self.table.currentItem()) if hasattr(self, "table") else None
            self.reload_folder(
                "Folder updated",
                select_path=selected if selected and selected.exists() else None,
            )

    def has_active_trash_workers(self) -> bool:
        return any(worker.isRunning() for worker in self.trash_workers)

    def background_scanner_active(self) -> bool:
        dialogs = list(getattr(self, "duplicate_dialogs", [])) + list(getattr(self, "bad_file_dialogs", []))
        return any(dialog.worker and dialog.worker.isRunning() for dialog in dialogs)

    def go_back(self):
        if not self.back_stack or not self.folder:
            return
        target = self.back_stack.pop()
        self.forward_stack.append(self.folder)
        self.navigate_to_folder(target, add_history=False)

    def go_forward(self):
        if not self.forward_stack or not self.folder:
            return
        target = self.forward_stack.pop()
        self.back_stack.append(self.folder)
        self.navigate_to_folder(target, add_history=False)

    def update_navigation_buttons(self):
        self.back_btn.setEnabled(bool(self.back_stack))
        self.forward_btn.setEnabled(bool(self.forward_stack))

    def update_undo_button(self):
        if not hasattr(self, "undo_btn"):
            return
        self.undo_btn.setEnabled(bool(self.undo_stack))
        if self.undo_stack:
            self.undo_btn.setToolTip(f"Undo {self.undo_stack[-1].label} (Command-Z)")
        else:
            self.undo_btn.setToolTip("Undo last file operation (Command-Z)")

    def has_numbered_direct_files(self) -> bool:
        return any(strip_leading_indexes(info.name) != info.name for info in self.files)

    def update_numerate_button(self):
        if not hasattr(self, "unorder_btn"):
            return
        self.unorder_btn.setText("Denumerate" if self.has_numbered_direct_files() else "Numberate")

    def update_sort_button_labels(self):
        if not hasattr(self, "order_created_btn"):
            return
        created_label = "Order by Creation Date"
        size_label = "Order by Size"
        media_label = "Ungroup" if getattr(self, "media_grouped", False) else "Group by Media Type"
        if self.sort_mode == "created":
            created_label += " ↑" if self.sort_reverse else " ↓"
        elif self.sort_mode == "size":
            size_label += " ↑" if not self.sort_reverse else " ↓"
        if getattr(self, "media_grouped", False):
            media_label += " ✓"
        self.order_created_btn.setText(created_label)
        self.order_size_btn.setText(size_label)
        self.type_sort_btn.setText(media_label)

    def reorder_to_folder_order(self):
        self.sort_mode = "name"
        self.sort_reverse = False
        self.media_grouped = False
        self.update_sort_button_labels()
        self.reload_folder("Sorted by name")

    def toggle_sort_by_creation_date(self):
        if self.sort_mode == "created":
            self.sort_reverse = not self.sort_reverse
        else:
            self.sort_mode = "created"
            self.sort_reverse = False
        self.update_sort_button_labels()
        direction = "new to old" if self.sort_reverse else "old to new"
        self.reload_folder(f"Ordered by creation date: {direction}")

    def toggle_sort_by_size(self):
        if self.sort_mode == "size":
            self.sort_reverse = not self.sort_reverse
        else:
            self.sort_mode = "size"
            self.sort_reverse = False
        self.update_sort_button_labels()
        direction = "small to large" if self.sort_reverse else "large to small"
        self.reload_folder(f"Ordered by size: {direction}")

    def record_browser_action(self, action: BrowserAction):
        if not action.moves:
            self.update_undo_button()
            return
        self.undo_stack.append(action)
        self.redo_stack.clear()
        self.update_undo_button()

    def move_path_for_browser_action(self, source: Path, destination: Path) -> Optional[Path]:
        if not source.exists():
            return None
        try:
            destination.parent.mkdir(parents=True, exist_ok=True)
            final_destination = unique_path(destination) if destination.exists() else destination
            shutil.move(str(source), str(final_destination))
            return final_destination
        except OSError:
            return None

    def remove_empty_created_dirs(self, dirs: List[Path]):
        for folder in sorted(dirs, key=lambda path: len(path.parts), reverse=True):
            try:
                folder.rmdir()
            except OSError:
                pass

    def undo_browser_action(self):
        if not self.undo_stack:
            self.update_undo_button()
            return

        action = self.undo_stack.pop()
        restored_moves: List[FileOperationMove] = []
        remaining_moves: List[FileOperationMove] = []
        for move in reversed(action.moves):
            final_path = self.move_path_for_browser_action(move.after, move.before)
            if final_path is not None:
                move.before = final_path
                restored_moves.append(move)
            else:
                remaining_moves.append(move)

        if restored_moves:
            self.remove_empty_created_dirs(action.created_dirs)
            self.redo_stack.append(
                BrowserAction(
                    action.label,
                    list(reversed(restored_moves)),
                    sends_to_trash=action.sends_to_trash,
                    created_dirs=list(action.created_dirs),
                )
            )
            self.reload_folder(f"Undid {action.label}: restored {human_count(len(restored_moves))} item(s)")
        if remaining_moves:
            self.undo_stack.append(
                BrowserAction(
                    action.label,
                    list(reversed(remaining_moves)),
                    sends_to_trash=action.sends_to_trash,
                    created_dirs=list(action.created_dirs),
                )
            )
        self.update_undo_button()

    def redo_browser_action(self):
        if not self.redo_stack:
            self.update_undo_button()
            return

        action = self.redo_stack.pop()
        changed_moves: List[FileOperationMove] = []
        remaining_moves: List[FileOperationMove] = []
        if action.sends_to_trash:
            for move in action.moves:
                if not move.before.exists():
                    remaining_moves.append(move)
                    continue
                trash_move = move_to_trash_recorded(move.before)
                if trash_move:
                    move.before = trash_move.original
                    move.after = trash_move.trash
                    changed_moves.append(move)
                else:
                    remaining_moves.append(move)
        else:
            for move in action.moves:
                final_path = self.move_path_for_browser_action(move.before, move.after)
                if final_path is not None:
                    move.after = final_path
                    changed_moves.append(move)
                else:
                    remaining_moves.append(move)

        if changed_moves:
            self.undo_stack.append(
                BrowserAction(
                    action.label,
                    changed_moves,
                    sends_to_trash=action.sends_to_trash,
                    created_dirs=list(action.created_dirs),
                )
            )
            self.reload_folder(f"Redid {action.label}: changed {human_count(len(changed_moves))} item(s)")
        if remaining_moves:
            self.redo_stack.append(
                BrowserAction(
                    action.label,
                    remaining_moves,
                    sends_to_trash=action.sends_to_trash,
                    created_dirs=list(action.created_dirs),
                )
            )
        self.update_undo_button()

    def browser_group_key(self, item: Optional[QTreeWidgetItem]) -> Optional[str]:
        """Stable key for virtual grouping rows so open/closed state survives reloads."""
        if not item:
            return None
        key = item.data(0, self.ROLE_GROUP_KEY)
        if key:
            return str(key)
        kind = self.browser_item_kind(item)
        path = self.browser_item_path(item)
        if path and kind in {"folder", "folder-child"}:
            try:
                return f"path:{path.expanduser().resolve()}"
            except OSError:
                return f"path:{path.expanduser().absolute()}"
        return None

    def capture_browser_open_state(self) -> set[str]:
        """Remember exactly which containers are open before a refresh/action.

        Actions operate on opened/visible files, so refreshing the table after an
        action must not fold those opened folders/headers back up. This snapshot
        is intentionally based on stable paths/group keys, not row numbers, so it
        survives sorting, renumbering, and watcher reloads.
        """
        opened: set[str] = set()
        if not hasattr(self, "table"):
            return opened

        def visit(item: QTreeWidgetItem):
            if self.is_browser_container_item(item) and item.isExpanded():
                key = self.browser_group_key(item)
                if key:
                    opened.add(key)
            for child_index in range(item.childCount()):
                visit(item.child(child_index))

        for top_index in range(self.table.topLevelItemCount()):
            visit(self.table.topLevelItem(top_index))
        return opened

    def restore_browser_open_state(self, opened: Optional[set[str]]):
        if not opened:
            return

        def restore(item: QTreeWidgetItem):
            if not self.is_browser_container_item(item):
                return
            key = self.browser_group_key(item)
            should_open = bool(key and key in opened)
            if should_open and self.browser_item_kind(item) in {"folder", "folder-child"}:
                self.populate_browser_folder_children(item)
            item.setExpanded(should_open)
            self.update_browser_folder_header(item)
            if should_open:
                for child_index in range(item.childCount()):
                    restore(item.child(child_index))

        for top_index in range(self.table.topLevelItemCount()):
            restore(self.table.topLevelItem(top_index))

    def reload_folder(self, status: str = "", select_path: Optional[Path] = None, select_index: Optional[int] = None):
        folder = self.require_folder()
        if not folder:
            return

        # Capture before scanning. If the external volume changes while this
        # refresh runs, the reconciliation timer will notice on its next pass.
        self.current_folder_entry_signature = direct_entry_signature(folder)
        open_state = self.capture_browser_open_state()
        self.files, self.summary = scan_folder(folder)
        self.file_info_by_path = {info.path: info for info in self.files}
        self.populate_table(select_path=select_path, select_index=select_index, open_state=open_state)
        self.populate_metrics()
        self.update_selection_details()
        self.update_empty_state()
        self.update_navigation_buttons()
        self.update_undo_button()

        if status:
            self.status.setText(status)
        else:
            self.status.setText(f"Showing {human_count(len(self.files))} direct file(s)")

    def update_empty_state(self):
        enabled = bool(self.folder and self.folder.exists())
        operation_running = bool(self.operation_worker and self.operation_worker.isRunning())
        for button in [
            self.reorder_btn,
            self.order_created_btn,
            self.order_size_btn,
            self.unorder_btn,
            self.type_sort_btn,
            self.dup_btn,
            self.bad_scan_btn,
            self.copy_path_btn,
        ]:
            button.setEnabled(enabled)
        for button in [self.reorder_btn, self.order_created_btn, self.order_size_btn, self.unorder_btn, self.type_sort_btn]:
            button.setEnabled(enabled and not operation_running)
        if self.copy_path_feedback_active:
            self.copy_path_btn.setEnabled(False)
        if hasattr(self, "terminate_btn"):
            self.terminate_btn.setEnabled(
                bool(
                    self.table_populate_timer.isActive()
                    or self.pending_table_entries
                    or (self.operation_worker and self.operation_worker.isRunning())
                    or self.has_active_trash_workers()
                )
            )
        self.update_numerate_button()
        self.update_sort_button_labels()
        self.update_navigation_buttons()
        self.update_auxiliary_window_buttons(enabled)

        if not enabled:
            self.file_card.set_metric("--", "No folder")
            self.size_card.set_metric("--", "")
            self.type_card.set_metric("--", "")
            self.index_card.set_metric("--", "")
            self.range_card.set_metric("--", "")
            self.clear_details()

    def show_task_progress(self, text: str, value: int = 0):
        # Bar-only progress in the action row. Keep text out of this cramped
        # strip so Bad File Scan -> Terminate stays clean and fixed.
        self.task_progress.setVisible(True)
        self.task_progress.setToolTip(text or "Working")
        self.task_progress.setValue(max(0, min(100, value)))
        if hasattr(self, "terminate_btn"):
            self.terminate_btn.setEnabled(True)

    def hide_task_progress(self):
        if self.operation_worker and self.operation_worker.isRunning():
            return
        if self.has_active_trash_workers():
            return
        if self.pending_table_entries:
            return
        self.task_progress.setVisible(False)
        if hasattr(self, "terminate_btn"):
            self.terminate_btn.setEnabled(False)

    def terminate_current_action(self):
        stopped = False
        if self.table_populate_timer.isActive() or self.pending_table_entries:
            self.table_populate_timer.stop()
            self.pending_table_entries = []
            self.pending_table_total = 0
            self.pending_table_select_path = None
            self.pending_table_select_index = None
            self.table_reloading = False
            stopped = True

        if self.operation_worker and self.operation_worker.isRunning():
            self.status.setText("Terminating and undoing current file operation")
            self.show_task_progress("Terminating: undoing changes", 0)
            self.operation_worker.request_cancel()
            self.operation_worker.requestInterruption()
            stopped = True

        for worker in list(self.trash_workers):
            if worker.isRunning():
                worker.requestInterruption()
                stopped = True

        if stopped:
            if not (self.operation_worker and self.operation_worker.isRunning()) and not self.has_active_trash_workers():
                self.hide_task_progress()
                self.reload_folder("Terminated current action")
        else:
            self.status.setText("No action is running")
        self.update_empty_state()

    def populate_table(self, select_path: Optional[Path] = None, select_index: Optional[int] = None, open_state: Optional[set[str]] = None):
        folder = self.folder
        if not folder:
            return

        self.table_reloading = True
        if self.table_populate_timer.isActive():
            self.table_populate_timer.stop()
        self.pending_table_entries = []
        self.pending_table_total = 0
        self.pending_table_select_path = select_path
        self.pending_table_select_index = select_index
        self.pending_table_open_state = open_state or set()
        self.table.clear()
        self.table.setHeaderLabels(self.TABLE_HEADERS)
        self._current_media_item = None
        self._current_ext_item = None

        child_folders = list_child_folders(folder)
        if self.sort_mode != "folder":
            child_folders = sorted(child_folders, key=natural_path_key)
        self.request_folder_metric_batch(child_folders)
        child_files = self.sorted_direct_files(list_files(folder))
        if getattr(self, "media_grouped", False):
            entries: List[Tuple[str, Optional[Path]]] = [("folder", path) for path in child_folders]
            media_groups: Dict[str, Dict[str, List[Path]]] = defaultdict(lambda: defaultdict(list))
            for file_path in child_files:
                kind_name = kind_for_path(file_path)
                ext_name = file_path.suffix.lower().lstrip(".") or "none"
                media_groups[kind_name][ext_name].append(file_path)
            for kind_name in sorted(media_groups.keys(), key=natural_text_key):
                kind_total = sum(len(group) for group in media_groups[kind_name].values())
                entries.append((f"media:{kind_name}:{kind_total}", None))
                for ext_name in sorted(media_groups[kind_name].keys(), key=natural_text_key):
                    ext_files = media_groups[kind_name][ext_name]
                    entries.append((f"ext:{kind_name}:{ext_name}:{len(ext_files)}", None))
                    entries.extend(("file", path) for path in ext_files)
        else:
            entries = [("folder", path) for path in child_folders]
            entries.extend(("file", path) for path in child_files)

        if len(entries) > 220:
            self.pending_table_entries = entries
            self.pending_table_total = len(entries)
            self.show_task_progress(f"Loading list 0/{human_count(len(entries))}", 0)
            self.table_populate_timer.start(0)
            return

        for kind, path in entries:
            self.add_browser_table_entry(kind, path)
        self.restore_browser_open_state(open_state)
        self.table_reloading = False
        self.select_browser_after_reload(select_path, select_index)
        if select_path is None and select_index is None:
            self.update_selection_details()

    def populate_table_chunk(self):
        if not self.pending_table_entries:
            self.table_populate_timer.stop()
            self.restore_browser_open_state(getattr(self, "pending_table_open_state", set()))
            self.pending_table_open_state = set()
            self.table_reloading = False
            if self.pending_table_select_path and self.select_path_in_browser_tree(self.pending_table_select_path):
                pass
            else:
                self.select_browser_after_reload(self.pending_table_select_path, self.pending_table_select_index)
            self.pending_table_select_path = None
            self.pending_table_select_index = None
            self.hide_task_progress()
            return

        chunk_size = 120
        chunk = self.pending_table_entries[:chunk_size]
        del self.pending_table_entries[:chunk_size]
        for kind, path in chunk:
            self.add_browser_table_entry(kind, path)

        done = self.pending_table_total - len(self.pending_table_entries)
        value = int(100 * done / max(1, self.pending_table_total))
        self.show_task_progress(
            f"Loading list {human_count(done)}/{human_count(self.pending_table_total)}",
            value,
        )

    def add_browser_table_entry(self, kind: str, path: Optional[Path]):
        if kind == "folder" and path is not None:
            header = self.browser_folder_header_item(path)
            self.table.addTopLevelItem(header)
            # Folder rows own real Kind and Size cells. Spanning column zero hid
            # those values even after the background metric worker supplied them.
            header.setFirstColumnSpanned(False)
            header.setExpanded(False)
            self.update_browser_folder_header(header)
            self._current_media_item = None
            self._current_ext_item = None
        elif kind.startswith("media:"):
            parts = kind.split(":")
            media_kind = parts[1] if len(parts) > 1 else "Media"
            count = int(parts[2]) if len(parts) > 2 and parts[2].isdigit() else sum(1 for info in self.files if info.kind == media_kind)
            item = QTreeWidgetItem([f"▼ {media_kind} ({human_count(count)} file(s))", "", "", "", "", ""])
            item.setData(0, self.ROLE_KIND, "media-header")
            item.setData(0, self.ROLE_LOADED, True)
            item.setData(0, self.ROLE_GROUP_KEY, f"media:{media_kind}")
            item.setFirstColumnSpanned(True)
            item.setExpanded(True)
            for column in range(self.table.columnCount()):
                item.setBackground(column, QColor("#303038"))
                item.setForeground(column, QColor("#f4f4f6"))
                font = item.font(column)
                font.setBold(True)
                item.setFont(column, font)
                item.setSizeHint(column, QSize(0, 30))
            self.table.addTopLevelItem(item)
            self._current_media_item = item
            self._current_ext_item = None
        elif kind.startswith("ext:"):
            parts = kind.split(":")
            ext_name = parts[2] if len(parts) > 2 else "none"
            ext_count = int(parts[3]) if len(parts) > 3 and parts[3].isdigit() else 0
            display_ext = ext_name if ext_name == "none" else f".{ext_name}"
            count_text = f" ({human_count(ext_count)} file(s))" if ext_count else ""
            item = QTreeWidgetItem([f"▼ {display_ext}{count_text}", "", ext_name, "", "", ""])
            item.setData(0, self.ROLE_KIND, "media-ext-header")
            item.setData(0, self.ROLE_LOADED, True)
            item.setData(0, self.ROLE_GROUP_KEY, f"ext:{parts[1] if len(parts) > 1 else 'Media'}:{ext_name}")
            item.setFirstColumnSpanned(True)
            item.setExpanded(True)
            for column in range(self.table.columnCount()):
                item.setBackground(column, QColor("#292930"))
                item.setForeground(column, QColor("#dfe0ea"))
                font = item.font(column)
                font.setBold(True)
                item.setFont(column, font)
                item.setSizeHint(column, QSize(0, 28))
            parent = getattr(self, "_current_media_item", None)
            if parent is not None:
                parent.addChild(item)
            else:
                self.table.addTopLevelItem(item)
            self._current_ext_item = item
        elif path is not None:
            file_item = self.browser_path_item(path)
            if getattr(self, "media_grouped", False) and getattr(self, "_current_ext_item", None) is not None and path.is_file():
                self._current_ext_item.addChild(file_item)
            else:
                self.table.addTopLevelItem(file_item)

    def visible_browser_items_in_order(self) -> List[QTreeWidgetItem]:
        items: List[QTreeWidgetItem] = []

        def add_visible(item: QTreeWidgetItem):
            items.append(item)
            if item.isExpanded():
                for child_index in range(item.childCount()):
                    add_visible(item.child(child_index))

        for top_index in range(self.table.topLevelItemCount()):
            add_visible(self.table.topLevelItem(top_index))
        return items

    def select_browser_after_reload(self, select_path: Optional[Path] = None, select_index: Optional[int] = None):
        items = self.visible_browser_items_in_order()
        if not items:
            return
        target = None
        if select_path:
            for item in items:
                if self.browser_item_path(item) == select_path:
                    target = item
                    break
        if target is None and select_index is not None:
            target = items[max(0, min(select_index, len(items) - 1))]
        if target is None:
            return
        self.table.clearSelection()
        target.setSelected(True)
        self.table.setCurrentItem(target)
        self.table.scrollToItem(target)
        self.current_browser_active_path = self.browser_item_path(target)
        QTimer.singleShot(0, self.update_selection_details)

    def select_path_in_browser_tree(self, target_path: Path) -> bool:
        def visit(item: QTreeWidgetItem, ancestors: List[QTreeWidgetItem]) -> Optional[QTreeWidgetItem]:
            if self.browser_item_path(item) == target_path:
                for ancestor in ancestors:
                    if not ancestor.isExpanded():
                        if self.browser_item_kind(ancestor) == "folder":
                            self.populate_browser_folder_children(ancestor)
                        ancestor.setExpanded(True)
                        self.update_browser_folder_header(ancestor)
                return item
            path = self.browser_item_path(item)
            if path and target_path.parent == path and self.browser_item_kind(item) == "folder":
                self.populate_browser_folder_children(item)
                item.setExpanded(True)
                self.update_browser_folder_header(item)
            for child_index in range(item.childCount()):
                found = visit(item.child(child_index), ancestors + [item])
                if found is not None:
                    return found
            return None

        for top_index in range(self.table.topLevelItemCount()):
            found = visit(self.table.topLevelItem(top_index), [])
            if found is not None:
                self.table.clearSelection()
                found.setSelected(True)
                self.table.setCurrentItem(found)
                self.table.scrollToItem(found)
                self.current_browser_active_path = target_path
                self.update_selection_details()
                return True
        return False

    def sorted_direct_files(self, files: List[Path]) -> List[Path]:
        if self.sort_mode == "folder":
            return files
        name_sorted = sorted(files, key=lambda path: natural_text_key(strip_order_prefixes(path.name)))
        if self.sort_mode == "created":
            return sorted(
                name_sorted,
                key=sortable_creation_time,
                reverse=self.sort_reverse,
            )
        if self.sort_mode == "size":
            return sorted(
                name_sorted,
                key=sortable_file_size,
                reverse=not self.sort_reverse,
            )
        return sorted(files, key=natural_path_key)

    def browser_folder_header_item(self, path: Path) -> QTreeWidgetItem:
        info = folder_info(path)
        created = date_text(info.created) if info else "?"
        modified = date_text(info.modified) if info else "?"
        item = QTreeWidgetItem(
            [
                f"▶ Folder: {folder_display_name(path.name)}",
                "Folder",
                "",
                "Calculating...",
                created,
                modified,
            ]
        )
        item.setData(0, self.ROLE_KIND, "folder")
        item.setData(0, self.ROLE_PATH, str(path))
        item.setData(0, self.ROLE_LOADED, False)
        item.setChildIndicatorPolicy(QTreeWidgetItem.ShowIndicator)
        item.setTextAlignment(0, Qt.AlignLeft | Qt.AlignVCenter)
        for column in range(self.table.columnCount()):
            item.setBackground(column, QColor("#2b2b2b"))
            item.setForeground(column, QColor("#f4f4f6"))
            font = item.font(column)
            font.setBold(True)
            item.setFont(column, font)
            item.setSizeHint(column, QSize(0, 32))
            item.setToolTip(column, str(path))
        item.setFlags(item.flags() | Qt.ItemIsEditable)
        return item

    def populate_browser_folder_children(self, item: QTreeWidgetItem):
        if self.browser_item_kind(item) not in {"folder", "folder-child"} or item.data(0, self.ROLE_LOADED):
            return
        path = self.browser_item_path(item)
        if not path:
            return
        try:
            raw_children = [p for p in path.iterdir() if not is_ignored_fs_entry(p)]
            child_dirs = sorted([p for p in raw_children if p.is_dir()], key=natural_path_key)
            child_files = self.sorted_direct_files([p for p in raw_children if p.is_file()])
            children = child_dirs + child_files
        except OSError:
            children = []

        for child in children:
            if child.is_file() or child.is_dir():
                item.addChild(self.browser_path_item(child))
        item.setData(0, self.ROLE_LOADED, True)

    @staticmethod
    def browser_file_values(path: Path) -> List[str]:
        """Use the same file columns when inserting and renaming a row."""
        info = file_info(path)
        if info is None:
            return [path.name, "?", path.suffix.lower().lstrip(".") or "none", "?", "?", "?"]
        return [
            info.name,
            info.kind,
            info.extension,
            human_size(info.size),
            date_text(info.created),
            date_text(info.modified),
        ]

    def browser_path_item(self, path: Path) -> QTreeWidgetItem:
        if path.is_dir():
            info = folder_info(path)
            values = [
                f"▶ {path.name}",
                "Folder",
                "",
                "Calculating...",
                date_text(info.created) if info else "?",
                date_text(info.modified) if info else "?",
            ]
            kind = "folder-child"
        else:
            values = self.browser_file_values(path)
            kind = "file"
        item = QTreeWidgetItem(values)
        item.setFlags(item.flags() | Qt.ItemIsEditable)
        item.setData(0, self.ROLE_KIND, kind)
        item.setData(0, self.ROLE_PATH, str(path))
        if kind == "folder-child":
            item.setData(0, self.ROLE_LOADED, False)
            item.setChildIndicatorPolicy(QTreeWidgetItem.ShowIndicator)
        for column, value in enumerate(values):
            item.setToolTip(column, str(path) if column == 0 else value)
        if path.is_dir():
            item.setForeground(0, QColor("#f4f4f6"))
        for col in (3, 4, 5):
            item.setTextAlignment(col, Qt.AlignRight | Qt.AlignVCenter)
        return item

    def update_browser_folder_header(self, item: QTreeWidgetItem):
        kind = self.browser_item_kind(item)
        marker = "▼" if item.isExpanded() else "▶"
        if kind in {"media-header", "media-ext-header"}:
            text = item.text(0)
            stripped = text[1:].strip() if text.startswith(("▼", "▶")) else text.strip()
            item.setText(0, f"{marker} {stripped}")
            for column in range(self.table.columnCount()):
                item.setToolTip(column, item.text(0))
            return
        path = self.browser_item_path(item)
        if not path:
            return
        if kind not in {"folder", "folder-child"}:
            return
        if kind == "folder-child":
            # Keep nested folder labels the same width before and after opening.
            # Appending counts only after the first click changed the horizontal
            # extent of the row and was a major source of the visible jitter.
            text = f"{marker} {folder_display_name(path.name)}"
            item.setText(0, text)
            for column in range(self.table.columnCount()):
                item.setToolTip(column, str(path))
            return

        try:
            file_count = len([p for p in path.iterdir() if p.is_file() and not is_ignored_fs_entry(p)])
            folder_count = len([p for p in path.iterdir() if p.is_dir() and not is_ignored_fs_entry(p)])
            text = f"{marker} Folder: {folder_display_name(path.name)} ({folder_count} folders, {file_count} files)"
            item.setText(0, text)
        except OSError:
            text = f"{marker} Folder: {folder_display_name(path.name)}"
            item.setText(0, text)
        for column in range(self.table.columnCount()):
            item.setToolTip(column, f"{text}\n{path}")

    def browser_item_path(self, item: Optional[QTreeWidgetItem]) -> Optional[Path]:
        if not item:
            return None
        path_text = item.data(0, self.ROLE_PATH)
        return Path(path_text) if path_text else None

    def browser_item_kind(self, item: Optional[QTreeWidgetItem]) -> str:
        return str(item.data(0, self.ROLE_KIND) or "") if item else ""

    def is_browser_container_item(self, item: Optional[QTreeWidgetItem]) -> bool:
        """Rows that can be opened/closed and whose open state should survive refreshes."""
        return self.browser_item_kind(item) in {
            "folder",
            "folder-child",
            "media-header",
            "media-ext-header",
            "group",
            "subgroup",
        }

    def toggle_browser_folder_header(self, item: QTreeWidgetItem):
        kind = self.browser_item_kind(item)
        if kind not in {"folder", "folder-child", "media-header", "media-ext-header"}:
            return

        expanding = not item.isExpanded()
        if expanding and kind in {"folder", "folder-child"}:
            self.populate_browser_folder_children(item)
        item.setExpanded(expanding)
        self.update_browser_folder_header(item)
        self.refresh_metrics_for_current_view()
        self.table.viewport().update()

    def on_browser_item_double_clicked(self, item: QTreeWidgetItem, _column: int = 0):
        # Native double-click timing again: double-clicking a real folder opens it.
        kind = self.browser_item_kind(item)
        path = self.browser_item_path(item)
        if kind in {"folder", "folder-child"}:
            if path and path.is_dir():
                self.navigate_to_folder(path, add_history=True)
            return
        if kind in {"media-header", "media-ext-header"}:
            # Virtual grouping headers have nowhere to navigate, so double-click keeps
            # the same expand/collapse meaning as a normal disclosure row.
            self.toggle_browser_folder_header(item)
            return
        if not path:
            return
        if path.is_dir():
            self.navigate_to_folder(path, add_history=True)
        else:
            self.open_browser_path(path)

    def rename_current_browser_item(self):
        item = self.table.currentItem()
        path = self.browser_item_path(item)
        if not item or not path:
            return
        kind = self.browser_item_kind(item)
        if kind not in {"file", "folder", "folder-child"}:
            return
        if not path.exists():
            self.status.setText("That item no longer exists")
            return
        self.browser_rename_item = item
        self.browser_rename_path = path
        if kind in {"folder", "folder-child"}:
            self.browser_rename_suppress = True
            try:
                item.setText(0, path.name)
            finally:
                self.browser_rename_suppress = False
        self.table.editItem(item, 0)

    def on_browser_rename_editor_closed(self, *_args):
        # Escape/cancel does not emit itemChanged. Restore the decorated display
        # label after the editor has actually left the tree item.
        QTimer.singleShot(0, self.restore_cancelled_browser_rename)

    def restore_cancelled_browser_rename(self):
        item = self.browser_rename_item
        path = self.browser_rename_path
        if item is None or path is None:
            return
        self.browser_rename_item = None
        self.browser_rename_path = None
        self.update_browser_path_item(item, path)

    def on_browser_item_changed(self, item: QTreeWidgetItem, column: int):
        if self.browser_rename_suppress:
            return
        if column != 0 or item is not self.browser_rename_item or self.browser_rename_path is None:
            return

        original = self.browser_rename_path
        self.browser_rename_item = None
        self.browser_rename_path = None

        new_name = re.sub(r"^[▼▶]\s*", "", item.text(0).strip()).strip()
        if not new_name or "/" in new_name or new_name in {".", ".."}:
            self.status.setText("Invalid file name")
            self.update_browser_path_item(item, original)
            return
        if new_name == original.name:
            self.update_browser_path_item(item, original)
            return

        target = original.with_name(new_name)
        if target.exists():
            target = unique_path(target)
        try:
            original.rename(target)
        except (OSError, ValueError) as exc:
            self.status.setText(f"Rename failed: {exc}")
            self.update_browser_path_item(item, original)
            return

        self.record_browser_action(BrowserAction("Rename", [FileOperationMove(before=original, after=target)]))
        self.replace_browser_path_reference(original, target)
        self.reload_folder(f"Renamed {original.name}", select_path=target)

    def update_browser_path_item(self, item: QTreeWidgetItem, path: Path):
        self.browser_rename_suppress = True
        try:
            kind = self.browser_item_kind(item)
            item.setData(0, self.ROLE_PATH, str(path))
            if path.is_dir():
                info = folder_info(path)
                if kind == "folder":
                    item.takeChildren()
                    item.setData(0, self.ROLE_LOADED, False)
                item.setChildIndicatorPolicy(QTreeWidgetItem.ShowIndicator)
                self.update_browser_folder_header(item)
                values = [
                    item.text(0),
                    "Folder",
                    "",
                    "Calculating...",
                    date_text(info.created) if info else "?",
                    date_text(info.modified) if info else "?",
                ]
            else:
                values = self.browser_file_values(path)
            for column, value in enumerate(values):
                item.setText(column, value)
                item.setToolTip(column, str(path) if column == 0 else value)
        finally:
            self.browser_rename_suppress = False

    def replace_browser_path_reference(self, before: Path, after: Path):
        for item in self.visible_browser_items_in_order():
            if self.browser_item_path(item) == before:
                self.update_browser_path_item(item, after)
        if self.current_browser_active_path == before:
            self.current_browser_active_path = after
        if self.previous_browser_active_path == before:
            self.previous_browser_active_path = after
        if self.pending_browser_preview_path == before:
            self.pending_browser_preview_path = after
        if (
            self.quicklook_dialog
            and self.quicklook_dialog.isVisible()
            and self.quicklook_dialog.effective_path() == before
        ):
            self.quicklook_dialog.set_path(after)

    def selected_browser_paths(self, include_header_children: bool = False) -> List[Path]:
        paths: List[Path] = []
        seen = set()
        for item in self.table.selectedItems():
            path = self.browser_item_path(item)
            if not path:
                continue
            if include_header_children and self.browser_item_kind(item) == "folder":
                for child_path in self.paths_under_folder_header(item):
                    if child_path not in seen:
                        paths.append(child_path)
                        seen.add(child_path)
            if path not in seen:
                paths.append(path)
                seen.add(path)
        return paths

    def paths_under_folder_header(self, item: QTreeWidgetItem) -> List[Path]:
        root = self.browser_item_path(item)
        if not root:
            return []
        paths = []
        try:
            for child in root.iterdir():
                if not is_ignored_fs_entry(child):
                    paths.append(child)
        except OSError:
            pass
        return paths

    def open_browser_context_menu(self, position):
        item = self.table.itemAt(position)
        if not item:
            return
        if not item.isSelected():
            self.table.clearSelection()
            item.setSelected(True)
            self.table.setCurrentItem(item)

        selected_paths = self.selected_browser_paths(include_header_children=False)
        menu = QMenu(self)
        open_action = menu.addAction("Open")
        preview_action = menu.addAction("Preview")
        reveal_action = menu.addAction("Reveal in Finder")
        menu.addSeparator()
        delete_action = menu.addAction("Move Selected to Trash" if len(selected_paths) > 1 else "Move to Trash")
        chosen = menu.exec(self.table.viewport().mapToGlobal(position))

        if chosen == open_action:
            self.open_browser_current_item()
        elif chosen == preview_action:
            self.preview_browser_current_item(toggle=False)
        elif chosen == reveal_action:
            path = self.browser_item_path(item)
            if path:
                reveal_in_finder(path)
        elif chosen == delete_action:
            self.move_browser_selection_to_trash()

    def open_browser_current_item(self):
        item = self.table.currentItem()
        if not item:
            return
        path = self.browser_item_path(item)
        if not path:
            return
        if path.is_dir():
            self.navigate_to_folder(path, add_history=True)
        else:
            self.open_browser_path(path)

    def preview_browser_current_item(self, toggle: bool = True):
        path = self.current_browser_file_path()
        if not path:
            return
        if toggle:
            now = time.monotonic()
            if now - self.last_preview_toggle_at < 0.22:
                return
            self.last_preview_toggle_at = now
        if (
            toggle
            and self.quicklook_dialog
            and self.quicklook_dialog.isVisible()
            and self.quicklook_dialog.effective_path() == path
        ):
            debug_log(
                "response",
                "browser preview window closing from Space",
                force=True,
            )
            self.quicklook_dialog.close()
            return
        self.zoom_browser_preview(path)

    def open_browser_path(self, path: Path):
        open_file_reusing_finder(path)
        self.table.setFocus(Qt.OtherFocusReason)

    def toggle_active_preview_playback(self):
        if self.quicklook_dialog and self.quicklook_dialog.isVisible():
            self.quicklook_dialog.toggle_video_playback()
        else:
            self.preview_panel.toggle_media_playback()

    def clear_browser_selection(self):
        self.browser_preview_timer.stop()
        self.pending_browser_preview_path = None
        self.preview_panel.reset()
        self.clear_details()
        if self.quicklook_dialog and self.quicklook_dialog.isVisible():
            self.quicklook_dialog.close()

    def schedule_browser_preview(self, path: Path):
        large_open = bool(self.quicklook_dialog and self.quicklook_dialog.isVisible())
        if (
            getattr(self.preview_panel, "current_path", None) == path
            and bool(getattr(self.preview_panel, "poster_only", False)) == large_open
        ):
            self.browser_preview_timer.stop()
            self.pending_browser_preview_path = None
            return
        self.pending_browser_preview_path = path
        self.browser_preview_timer.start(180 if self.background_scanner_active() else 150)

    def apply_pending_browser_preview(self):
        path = self.pending_browser_preview_path
        self.pending_browser_preview_path = None
        if not path or not path.exists():
            self.preview_panel.reset()
            return
        if self.quicklook_dialog and self.quicklook_dialog.isVisible():
            # Rapid table traversal must not create one decoder/proxy job per
            # transient row. The large preview applies only the settled target
            # and synchronizes the embedded paused poster at that same boundary.
            self.quicklook_dialog.queue_path(
                path,
                self.preview_panel.cached_media_metadata_if_ready(path),
            )
            return
        self.preview_panel.set_path(path, probe_media=not self.background_scanner_active())

    def restore_browser_preview_after_quicklook(self):
        self.table.preview_navigation_active = False
        path = self.current_browser_file_path()
        if path:
            panel = self.preview_panel
            same_live_preview = (
                getattr(panel, "current_path", None) == path
                and not bool(getattr(panel, "poster_only", False))
            )
            if same_live_preview:
                # Opening the separate preview temporarily pauses this player.
                # Restore the user's embedded browsing preference even when
                # the selected path did not change (the normal Quick Look case).
                panel.restore_browse_playback_preference()
            else:
                self.schedule_browser_preview(path)

    def drop_paths_into_current_folder(self, paths: List[Path]):
        folder = self.require_folder()
        if not folder:
            return
        moved = 0
        skipped = 0
        moves: List[FileOperationMove] = []
        folder_resolved = folder.resolve()
        for source in paths:
            if not source.exists():
                skipped += 1
                continue
            try:
                source_resolved = source.resolve()
            except OSError:
                skipped += 1
                continue
            try:
                source_parent_resolved = source.parent.resolve()
            except OSError:
                source_parent_resolved = source.parent.absolute()
            if source_parent_resolved == folder_resolved:
                # An internal drag of a direct row back onto its own table is a
                # no-op, not a request to manufacture a renamed duplicate.
                skipped += 1
                continue
            if source_resolved == folder_resolved or source_resolved in folder_resolved.parents:
                skipped += 1
                continue
            target = unique_path(folder / source.name)
            try:
                shutil.move(str(source), str(target))
                moves.append(FileOperationMove(before=source, after=target))
                moved += 1
            except OSError:
                skipped += 1
        if moved:
            self.record_browser_action(BrowserAction("Move Here", moves))
            self.reload_folder(f"Moved {human_count(moved)} item(s) here")
        elif skipped:
            self.status.setText("Nothing moved")

    def browser_file_items_in_order(self) -> List[QTreeWidgetItem]:
        items: List[QTreeWidgetItem] = []

        def collect(item: QTreeWidgetItem):
            path = self.browser_item_path(item)
            if path and path.is_file():
                items.append(item)
            if item.isExpanded():
                for child_index in range(item.childCount()):
                    collect(item.child(child_index))

        for top_index in range(self.table.topLevelItemCount()):
            collect(self.table.topLevelItem(top_index))
        return items

    def current_browser_file_path(self) -> Optional[Path]:
        item = self.table.currentItem()
        path = self.browser_item_path(item)
        if path and path.is_file():
            return path
        for selected in self.table.selectedItems():
            path = self.browser_item_path(selected)
            if path and path.is_file():
                return path
        return None

    def preview_adjacent_browser_file(self, direction: int, video_only: bool = False) -> bool:
        items = self.browser_file_items_in_order()
        if video_only:
            items = [
                item for item in items
                if (path := self.browser_item_path(item)) is not None and is_video_path(path)
            ]
        if not items:
            return False
        current = self.table.currentItem()
        try:
            index = items.index(current)
        except ValueError:
            current_path = self.current_browser_file_path()
            index = next((i for i, item in enumerate(items) if self.browser_item_path(item) == current_path), 0)
        next_index = index + direction
        if next_index < 0 or next_index >= len(items):
            return False
        target = items[next_index]
        self.table.clearSelection()
        target.setSelected(True)
        self.table.setCurrentItem(target)
        self.table.scrollToItem(target)
        path = self.browser_item_path(target)
        if path:
            if self.quicklook_dialog and self.quicklook_dialog.isVisible():
                self.quicklook_dialog.queue_path(path)
            else:
                self.schedule_browser_preview(path)
            return True
        return False

    def move_browser_selection_to_trash(self):
        paths = self.selected_browser_paths(include_header_children=False)
        if not paths:
            return
        paths = list(dict.fromkeys(paths))
        before_items = self.visible_browser_items_in_order()
        before_paths = [self.browser_item_path(item) for item in before_items]
        selected_indexes = [before_paths.index(path) for path in paths if path in before_paths]
        fallback_index = max(0, min(selected_indexes) - 1) if selected_indexes else 0
        preferred_path = None
        for candidate in reversed(before_paths[: min(selected_indexes) if selected_indexes else 0]):
            if candidate and candidate.exists() and candidate not in paths:
                preferred_path = candidate
                break
        self.remove_browser_paths_from_view(paths)
        if preferred_path and self.select_path_in_browser_tree(preferred_path):
            pass
        else:
            self.select_browser_after_reload(select_index=fallback_index)
        if not self.table.currentItem():
            self.clear_details()
            self.preview_panel.reset()
        self.start_background_trash_move(paths)

    def remove_browser_paths_from_view(self, paths: List[Path]):
        path_set = set(paths)
        if self.pending_table_entries:
            self.pending_table_entries = [
                (kind, path) for kind, path in self.pending_table_entries if path not in path_set
            ]
            self.pending_table_total = max(0, self.pending_table_total - len(path_set))

        def prune_children(parent: QTreeWidgetItem):
            for child_index in range(parent.childCount() - 1, -1, -1):
                child = parent.child(child_index)
                if self.browser_item_path(child) in path_set:
                    parent.takeChild(child_index)
                else:
                    prune_children(child)

        self.table.blockSignals(True)
        try:
            for top_index in range(self.table.topLevelItemCount() - 1, -1, -1):
                top = self.table.topLevelItem(top_index)
                if self.browser_item_path(top) in path_set:
                    self.table.takeTopLevelItem(top_index)
                    continue
                prune_children(top)
                if self.browser_item_kind(top) in {"folder", "media-header", "media-ext-header"}:
                    self.update_browser_folder_header(top)
        finally:
            self.table.blockSignals(False)

    def start_background_trash_move(self, paths: List[Path]):
        worker = TrashMoveWorker(paths)
        self.trash_workers.append(worker)
        worker.progress.connect(self.on_background_trash_progress)
        worker.results_ready.connect(
            lambda moves, failures, worker=worker: self.on_background_trash_finished(worker, moves, failures)
        )
        worker.finished.connect(
            lambda worker=worker, owners=self.trash_workers: retire_thread_worker(worker, owners)
        )
        worker.finished.connect(lambda: QTimer.singleShot(0, self.maybe_close_after_trash_moves))
        total = len(paths)
        self.show_task_progress(f"Moving to Trash 0/{human_count(total)}", 0)
        self.status.setText(f"Moving {human_count(total)} item(s) to Trash in background")
        worker.start()
        self.update_empty_state()

    def maybe_close_after_trash_moves(self):
        if self.closing_after_trash_moves and not self.has_active_trash_workers():
            self.closing_after_trash_moves = False
            QTimer.singleShot(0, self.close)

    def on_background_trash_progress(self, done: int, total: int):
        value = int(100 * done / max(1, total))
        self.show_task_progress(f"Moving to Trash {human_count(done)}/{human_count(total)}", value)

    def on_background_trash_finished(self, worker: TrashMoveWorker, moves: List[TrashMove], failures: List[Path]):
        operation_moves = [FileOperationMove(before=move.original, after=move.trash) for move in moves]
        if operation_moves:
            self.record_browser_action(BrowserAction("Move to Trash", operation_moves, sends_to_trash=True))

        moved_count = len(operation_moves)
        failed_count = len(failures)
        if failed_count:
            self.status.setText(
                f"Moved {human_count(moved_count)} item(s); {human_count(failed_count)} failed"
            )
        else:
            self.status.setText(f"Moved {human_count(moved_count)} item(s) to Trash")
        self.hide_task_progress()
        self.update_empty_state()
        if failed_count:
            self.reload_debounce.start(300)
        else:
            self.reload_debounce.start(1100)

    def select_path_from_card(self, path: Optional[Path], status: str = ""):
        if not path:
            return
        if self.select_path_in_browser_tree(path):
            if status:
                self.status.setText(status)
            return
        self.reload_folder(status or f"Selected {path.name}", select_path=path)

    def select_largest_item(self):
        if not self.summary or not self.summary.largest:
            return
        self.select_path_from_card(self.summary.largest.path, f"Selected largest item: {self.summary.largest.name}")

    def reveal_largest_item(self):
        if self.summary and self.summary.largest:
            reveal_in_finder(self.summary.largest.path)

    def select_oldest_item(self):
        if not self.summary or not self.summary.oldest:
            return
        self.sort_mode = "created"
        self.sort_reverse = False
        self.update_sort_button_labels()
        self.reload_folder(f"Selected oldest item: {self.summary.oldest.name}", select_path=self.summary.oldest.path)

    def select_newest_item(self):
        if not self.summary or not self.summary.newest:
            return
        self.sort_mode = "created"
        self.sort_reverse = True
        self.update_sort_button_labels()
        self.reload_folder(f"Selected newest item: {self.summary.newest.name}", select_path=self.summary.newest.path)

    def folder_visible_atom_info(self, path: Path) -> Optional[FileInfo]:
        """Represent a collapsed folder as one statistical atom.

        Directory inode sizes on macOS are tiny and visually useless for the
        histogram. For closed folders, use their recursive contents size so the
        top cards/statistics read like the user-visible object: the whole folder.
        Expanded folders still expose their children individually.
        """
        try:
            st = path.stat()
            cache_key = f"{path.resolve()}::{st.st_mtime_ns}"
        except OSError:
            return folder_info(path)

        cached = getattr(self, "folder_metric_cache", {}).get(cache_key)
        if cached is not None:
            return cached
        self.request_folder_metric(path, cache_key)
        return folder_info(path)

    def request_folder_metric(self, path: Path, cache_key: str):
        if cache_key in self.folder_metric_cache or cache_key in self.folder_metric_futures:
            return
        future = self.folder_metric_executor.submit(
            recursive_folder_info,
            path,
            self.folder_metric_cancel,
        )
        self.folder_metric_futures[cache_key] = future

        def deliver(completed, key=cache_key):
            try:
                info = completed.result()
                self.folder_metric_signals.ready.emit(key, info)
            except (RuntimeError, concurrent.futures.CancelledError):
                pass
            except Exception:
                try:
                    self.folder_metric_signals.ready.emit(key, None)
                except RuntimeError:
                    pass

        future.add_done_callback(deliver)

    def request_folder_metric_batch(self, paths: Sequence[Path]):
        pending: List[Tuple[str, Path]] = []
        for path in paths:
            try:
                stat = path.stat()
                cache_key = f"{path.resolve()}::{stat.st_mtime_ns}"
            except OSError:
                continue
            if cache_key in self.folder_metric_cache or cache_key in self.folder_metric_futures:
                continue
            pending.append((cache_key, Path(path)))
        if not pending:
            return
        if len(pending) == 1:
            cache_key, path = pending[0]
            self.request_folder_metric(path, cache_key)
            return

        future = self.folder_metric_executor.submit(
            recursive_folder_infos,
            [path for _cache_key, path in pending],
            self.folder_metric_cancel,
        )
        for cache_key, _path in pending:
            self.folder_metric_futures[cache_key] = future

        def deliver(completed, requested=pending):
            try:
                results = completed.result()
            except (RuntimeError, concurrent.futures.CancelledError):
                results = {}
            except Exception:
                results = {}
            for cache_key, path in requested:
                path_key = os.path.normpath(os.fspath(path))
                try:
                    self.folder_metric_signals.ready.emit(cache_key, results.get(path_key))
                except RuntimeError:
                    return

        future.add_done_callback(deliver)

    def on_folder_metric_ready(self, cache_key: str, info: Optional[FileInfo]):
        self.folder_metric_futures.pop(cache_key, None)
        if info is not None:
            self.folder_metric_cache[cache_key] = info
        if len(self.folder_metric_cache) > 2048:
            for key in list(self.folder_metric_cache.keys())[:256]:
                self.folder_metric_cache.pop(key, None)
        if self.folder and info is not None:
            self.metrics_refresh_timer.start(90)
            current_path = self.browser_item_path(self.table.currentItem()) if hasattr(self, "table") else None
            if current_path == info.path:
                self.update_selection_details()

    def visible_metric_infos(self) -> List[FileInfo]:
        """Return the visible statistical atoms for the current tree state.

        Expanded containers expose their children. Collapsed folders/headers are
        counted as one visible item. This keeps the top cards in sync with the
        same opened-scope model used by Numberate, scanners, and ordering.
        """
        if not hasattr(self, "table") or self.table.topLevelItemCount() == 0:
            return []

        def info_for_path(path: Optional[Path]) -> Optional[FileInfo]:
            if not path:
                return None
            return self.folder_visible_atom_info(path) if path.is_dir() else file_info(path)

        def aggregate_container(item: QTreeWidgetItem) -> Optional[FileInfo]:
            collected: List[FileInfo] = []

            def collect_descendants(node: QTreeWidgetItem):
                path = self.browser_item_path(node)
                if path:
                    info = info_for_path(path)
                    if info:
                        collected.append(info)
                    return
                for child_index in range(node.childCount()):
                    collect_descendants(node.child(child_index))

            for child_index in range(item.childCount()):
                collect_descendants(item.child(child_index))
            if not collected:
                return None

            label = re.sub(r"^[▼▶]\s*", "", item.text(0)).strip() or "Group"
            created = min(info.created for info in collected)
            modified = max(info.modified for info in collected)
            accessed = max(info.accessed for info in collected)
            size = sum(info.size for info in collected)
            kind = label.split("(", 1)[0].strip().lstrip(".") or "Group"
            # The path is only a harmless placeholder for statistics; clickable
            # actions still use real row paths, not these synthetic group rows.
            placeholder = self.folder or Path(".")
            return FileInfo(
                path=placeholder,
                name=label,
                extension="group",
                kind=kind,
                mime="application/x-folder-manager-group",
                size=size,
                created=created,
                modified=modified,
                accessed=accessed,
                indexed=False,
            )

        result: List[FileInfo] = []

        def visit(item: QTreeWidgetItem):
            path = self.browser_item_path(item)
            is_container = self.is_browser_container_item(item)
            if is_container:
                if item.isExpanded():
                    # A loaded expanded folder/header contributes its visible children.
                    # Empty expanded folders still appear as one folder atom.
                    before = len(result)
                    for child_index in range(item.childCount()):
                        visit(item.child(child_index))
                    if len(result) == before and path:
                        info = info_for_path(path)
                        if info:
                            result.append(info)
                else:
                    if path:
                        info = info_for_path(path)
                    else:
                        info = aggregate_container(item)
                    if info:
                        result.append(info)
                return
            if path:
                info = info_for_path(path)
                if info:
                    result.append(info)

        for top_index in range(self.table.topLevelItemCount()):
            visit(self.table.topLevelItem(top_index))
        return result

    def visible_metric_summary(self) -> Optional[FolderSummary]:
        infos = self.visible_metric_infos()
        if not infos:
            return None
        kind_counts: Counter = Counter(info.kind for info in infos)
        kind_sizes: Counter = Counter()
        for info in infos:
            kind_sizes[info.kind] += info.size
        real_infos = [info for info in infos if info.path and info.path.exists()]
        sortable = real_infos or infos
        return FolderSummary(
            file_count=sum(1 for info in infos if info.kind != "Folder"),
            folder_count=sum(1 for info in infos if info.kind == "Folder"),
            total_size=sum(info.size for info in infos),
            type_count=len(kind_counts),
            indexed_count=sum(1 for info in infos if info.indexed),
            largest=max(sortable, key=lambda info: info.size, default=None),
            oldest=min(sortable, key=lambda info: info.created, default=None),
            newest=max(sortable, key=lambda info: info.created, default=None),
            kind_counts=kind_counts,
            kind_sizes=kind_sizes,
        )

    def refresh_metrics_for_current_view(self, *_args):
        if getattr(self, "table_reloading", False):
            return
        # Coalesce the several expansion signals emitted during one disclosure
        # click and let the tree finish laying itself out before doing statistics.
        self.metrics_refresh_timer.start(55)

    def apply_metrics_refresh_for_current_view(self):
        if getattr(self, "table_reloading", False):
            return
        self.populate_metrics()

    def populate_metrics(self):
        if not self.summary:
            return

        view_summary = self.visible_metric_summary()
        summary = view_summary or self.summary
        metric_infos = self.visible_metric_infos() or self.files
        self.file_card.set_metric(
            human_count(summary.file_count),
            f"{human_count(summary.folder_count)} folder(s)",
        )
        largest_name = summary.largest.name if summary.largest else "--"
        self.size_card.set_metric(
            human_size(summary.total_size),
            f"Largest: {largest_name}",
        )
        self.size_card.setToolTip(
            f"Click to select largest item: {largest_name}\nDouble-click to reveal it in Finder"
            if summary.largest else "No largest item"
        )
        # Show every detected kind, not only the three most common ones. The
        # Types card can expand horizontally, while its tooltip always preserves
        # the complete list even when the window is at its minimum width.
        all_type_names = [kind for kind, _ in summary.kind_counts.most_common()]
        self.type_card.set_metric(
            human_count(summary.type_count),
            ", ".join(all_type_names) or "--",
        )
        histogram_bins, histogram_tooltip, histogram_labels = file_size_histogram(metric_infos)
        stats_meta = file_size_stats_text(metric_infos)
        self.index_card.set_statistics(histogram_bins, stats_meta, histogram_tooltip, histogram_labels)

        if summary.oldest and summary.newest:
            range_start, range_end = compact_date_range_text(summary.oldest, summary.newest)
            self.range_card.set_range(range_start, range_end)
        else:
            self.range_card.set_range("--", "--")
        self.apply_folder_size_progress()

    def cached_folder_metric_info(self, path: Path) -> Optional[FileInfo]:
        try:
            cache_key = f"{path.resolve()}::{path.stat().st_mtime_ns}"
        except OSError:
            return None
        return self.folder_metric_cache.get(cache_key)

    def apply_folder_size_progress(self):
        """Apply cached folder sizes without doing filesystem walks on the UI thread."""
        if not hasattr(self, "table"):
            return

        def item_size(item: QTreeWidgetItem) -> Optional[int]:
            path = self.browser_item_path(item)
            if not path:
                return None
            if path.is_file():
                try:
                    return path.stat().st_size
                except OSError:
                    return None
            cached = self.cached_folder_metric_info(path)
            if cached is not None:
                return cached.size
            if item.isExpanded() and item.childCount():
                child_sizes = [item_size(item.child(i)) for i in range(item.childCount())]
                if child_sizes and all(size is not None for size in child_sizes):
                    return sum(size for size in child_sizes if size is not None)
            return None

        def apply_siblings(items: List[QTreeWidgetItem]):
            sizes = {id(item): item_size(item) for item in items}
            total = sum(size for size in sizes.values() if size is not None)

            comparison_markers: Dict[int, str] = {}
            for candidate_kind in ("folder", "file"):
                candidates: List[Tuple[QTreeWidgetItem, int]] = []
                for candidate in items:
                    kind = self.browser_item_kind(candidate)
                    is_candidate = (
                        kind in {"folder", "folder-child"}
                        if candidate_kind == "folder"
                        else kind == "file"
                    )
                    size = sizes[id(candidate)]
                    if is_candidate and size is not None:
                        candidates.append((candidate, size))
                distinct_sizes = {size for _item, size in candidates}
                if len(candidates) < 2 or len(distinct_sizes) < 2:
                    continue
                smallest = min(distinct_sizes)
                largest = max(distinct_sizes)
                for candidate, size in candidates:
                    if size == largest:
                        comparison_markers[id(candidate)] = "▲ "
                    elif size == smallest:
                        comparison_markers[id(candidate)] = "▼ "

            for item in items:
                kind = self.browser_item_kind(item)
                size = sizes[id(item)]
                is_folder = kind in {"folder", "folder-child"}
                ratio = size / total if size is not None and total > 0 and is_folder else None
                item.setData(0, FOLDER_PROGRESS_ROLE, ratio)
                if is_folder or kind == "file":
                    size_text = human_size(size) if size is not None else "Calculating..."
                    marker = comparison_markers.get(id(item), "")
                    item.setText(3, f"{marker}{size_text}")
                    item.setToolTip(3, size_text)
                    item.setTextAlignment(3, Qt.AlignRight | Qt.AlignVCenter)
                    item.setForeground(3, QBrush())
                if item.childCount():
                    apply_siblings([item.child(i) for i in range(item.childCount())])

        apply_siblings([self.table.topLevelItem(i) for i in range(self.table.topLevelItemCount())])
        self.table.viewport().update()


    def selected_file_info(self) -> Optional[FileInfo]:
        item = self.table.currentItem()
        path = self.browser_item_path(item)
        if not path or not path.is_file():
            return None
        cached = getattr(self, "file_info_by_path", {}).get(path)
        if cached is not None:
            return cached
        return file_info(path)

    def schedule_selection_details_update(self):
        # One settled selection should launch one preview. This keeps keyboard
        # traversal and scanner list refreshes from creating obsolete ffprobe
        # jobs faster than the media backend can cancel them.
        self.selection_details_timer.start(45)

    def update_selection_details(self):
        current_path = self.browser_item_path(self.table.currentItem())
        if current_path:
            if current_path != self.debug_last_browser_selection_path:
                self.debug_last_browser_selection_path = current_path
                current_item = self.table.currentItem()
                debug_log(
                    "input",
                    "browser table row selected",
                    force=True,
                    row_kind=current_item.data(0, self.ROLE_KIND) if current_item else "none",
                    selected_rows=len(self.table.selectedItems()),
                    media_kind="folder" if current_path.is_dir() else kind_for_path(current_path),
                    preview_window_open=bool(
                        self.quicklook_dialog and self.quicklook_dialog.isVisible()
                    ),
                )
            if current_path != self.current_browser_active_path:
                if self.current_browser_active_path and self.current_browser_active_path.exists():
                    self.previous_browser_active_path = self.current_browser_active_path
                self.current_browser_active_path = current_path
            self.schedule_browser_preview(current_path)
        else:
            if (
                self.table_reloading
                or self.pending_table_entries
                or self.table_populate_timer.isActive()
                or (self.operation_worker and self.operation_worker.isRunning())
            ):
                return
            self.current_browser_active_path = None
            self.debug_last_browser_selection_path = None
            self.browser_preview_timer.stop()
            self.pending_browser_preview_path = None
            self.preview_panel.reset()

        self.reset_optional_detail_rows()

        if current_path and current_path.is_dir():
            self._update_folder_details(current_path)
            return

        info = self.selected_file_info()
        if info is None:
            self.clear_details()
            return
        self._update_file_details(info)

    def _update_folder_details(self, current_path: Path):
        info = self.cached_folder_metric_info(current_path)
        if info is None:
            try:
                stat = current_path.stat()
                cache_key = f"{current_path.resolve()}::{stat.st_mtime_ns}"
                self.request_folder_metric(current_path, cache_key)
            except OSError:
                pass
        stat_info = info or folder_info(current_path)
        try:
            folders = len(list_child_folders(current_path))
            files = len(list_files(current_path))
        except OSError:
            folders = 0
            files = 0
        self.detail_duration.set_label("Folders")
        self.detail_resolution.set_label("Files")
        self.detail_duration.setVisible(True)
        self.detail_resolution.setVisible(True)
        self.detail_sample_rate.setVisible(False)
        self.detail_name.set_value(current_path.name)
        self.detail_kind.set_value("Folder")
        self.detail_duration.set_value(f"{human_count(folders)} folder(s)")
        self.detail_resolution.set_value(f"{human_count(files)} file(s)")
        self.detail_size.set_value("Calculating..." if info is None else f"{human_size(info.size)} ({info.size:,} bytes)")
        self.detail_created.set_value("--" if not stat_info else date_text(stat_info.created))
        self.detail_modified.set_value("--" if not stat_info else date_text(stat_info.modified))
        self.detail_mime.set_value("inode/directory")
        self.detail_path.set_value(str(current_path))

    def _update_file_details(self, info: FileInfo):
        meta = MediaMeta()
        if info.kind in {"Image", "Video", "Audio"}:
            cached_meta = self.preview_panel.cached_media_metadata_if_ready(info.path)
            if cached_meta is not None:
                meta = cached_meta

        self._update_media_detail_rows(info.kind, meta)

        self.detail_name.set_value(info.name)
        self.detail_kind.set_value(f"{info.kind} / .{info.extension}" if info.extension != "none" else info.kind)
        self.detail_size.set_value(f"{human_size(info.size)} ({info.size:,} bytes)")
        self.detail_created.set_value(date_text(info.created))
        self.detail_modified.set_value(date_text(info.modified))
        self.detail_mime.set_value(info.mime)
        self.detail_path.set_value(str(info.path))

    def on_browser_preview_metadata_loaded(self, path: Path, meta: MediaMeta):
        if self.browser_item_path(self.table.currentItem()) != path:
            return
        info = self.selected_file_info()
        if info and info.path == path:
            self._update_media_detail_rows(info.kind, meta)

    def _update_media_detail_rows(self, kind: str, meta: MediaMeta):
        """Render only the metadata fields supported by this media kind."""
        rows = (
            (self.detail_duration, "Duration", meta.duration, kind in {"Video", "Audio"}),
            (
                self.detail_resolution,
                "Dimensions" if kind == "Image" else "Resolution",
                meta.resolution,
                kind in {"Video", "Image"},
            ),
            (self.detail_sample_rate, "Sample Rate", meta.sample_rate, kind in {"Video", "Audio"}),
        )
        for row, label, value, visible in rows:
            row.set_label(label)
            row.setVisible(visible)
            if visible:
                row.set_value(value or "--")

    def reset_optional_detail_rows(self):
        self.detail_duration.set_label("Duration")
        self.detail_resolution.set_label("Resolution")
        self.detail_sample_rate.set_label("Sample Rate")
        self.detail_duration.setVisible(True)
        self.detail_resolution.setVisible(True)
        self.detail_sample_rate.setVisible(True)

    def clear_details(self):
        self.reset_optional_detail_rows()
        for detail in self.detail_rows:
            detail.set_value("--")

    def confirm(self, title: str, text: str) -> bool:
        result = QMessageBox.question(
            self,
            title,
            text,
            QMessageBox.Yes | QMessageBox.No,
            QMessageBox.No,
        )
        return result == QMessageBox.Yes

    def start_rename_operation(
        self,
        label: str,
        pairs: List[Tuple[Path, Path]],
        created_dirs: Optional[List[Path]] = None,
    ):
        if self.operation_worker and self.operation_worker.isRunning():
            self.status.setText("A file operation is already running")
            return
        if not pairs:
            self.status.setText(f"{label}: no changes needed")
            return

        self.pending_operation_created_dirs = created_dirs or []
        self.show_task_progress(f"{label}: 0/{human_count(len(pairs))}", 0)
        self.operation_worker = RenameWorker(label, pairs)
        self.operation_worker.progress.connect(self.on_operation_progress)
        self.operation_worker.renamed.connect(self.on_operation_renamed)
        self.operation_worker.results_ready.connect(self.on_operation_finished)
        self.operation_worker.finished.connect(
            lambda worker=self.operation_worker: worker.deleteLater()
        )
        self.operation_worker.failed.connect(self.on_operation_failed)
        self.operation_worker.cancelled.connect(self.on_operation_cancelled)
        self.operation_worker.start()
        self.update_empty_state()

    def on_operation_progress(self, text: str, value: int):
        self.show_task_progress(text, value)
        self.status.setText(text)

    def on_operation_renamed(self, before: Path, after: Path):
        self.replace_browser_path_reference(before, after)

    def on_operation_finished(self, label: str, moves: List[FileOperationMove]):
        created_dirs = self.pending_operation_created_dirs
        self.pending_operation_created_dirs = []
        self.operation_worker = None
        if moves:
            self.record_browser_action(BrowserAction(label, moves, created_dirs=created_dirs))
        select_path = moves[-1].after if moves else None
        self.reload_folder(f"{label}: changed {human_count(len(moves))} item(s)", select_path=select_path)
        self.update_empty_state()
        self.hide_task_progress()

    def on_operation_failed(self, message: str):
        created_dirs = self.pending_operation_created_dirs
        self.pending_operation_created_dirs = []
        self.operation_worker = None
        self.remove_empty_created_dirs(created_dirs)
        self.update_empty_state()
        self.status.setText(f"Operation failed: {message}")
        self.show_task_progress("Operation failed", 0)
        QTimer.singleShot(1800, self.hide_task_progress)
        if self.closing_after_operation_cancel:
            self.closing_after_operation_cancel = False
            QTimer.singleShot(0, self.close)

    def on_operation_cancelled(self, label: str, rolled_back: int):
        created_dirs = self.pending_operation_created_dirs
        self.pending_operation_created_dirs = []
        self.operation_worker = None
        self.remove_empty_created_dirs(created_dirs)
        self.hide_task_progress()
        self.reload_folder(f"{label}: terminated, restored {human_count(rolled_back)} item(s)")
        self.update_empty_state()
        if self.closing_after_operation_cancel:
            self.closing_after_operation_cancel = False
            QTimer.singleShot(0, self.close)

    def number_files_by_groups(self, groups: List[List[Path]], label: str):
        groups = [[path for path in group if path and path.is_file()] for group in groups]
        groups = [group for group in groups if group]
        if not groups:
            self.status.setText("No files to numberate")
            return

        if not self.confirm(
            label,
            "This will numberate files in the current visible order. Existing leading numbers are removed first. In media headers, numbering restarts inside each header.",
        ):
            return

        pairs: List[Tuple[Path, Path]] = []
        for group in groups:
            for index, file in enumerate(group, start=1):
                clean_name = strip_order_prefixes(file.name)
                new_name = f"{index}. {clean_name}"
                dst = file.with_name(new_name)
                if dst.name != file.name:
                    pairs.append((file, dst))

        self.start_rename_operation(label, pairs)

    def visible_direct_file_paths(self) -> List[Path]:
        paths: List[Path] = []
        for item in self.visible_browser_items_in_order():
            path = self.browser_item_path(item)
            if path and path.is_file():
                paths.append(path)
        return paths

    def visible_direct_file_groups_for_numbering(self) -> List[List[Path]]:
        """Return rename groups from the currently opened/visible tree only.

        Collapsed folders/headers are treated as closed boxes: their descendants
        are not touched. Numbering restarts for each opened folder or media
        extension header, including nested expanded folders.
        """
        groups: List[List[Path]] = []
        top_direct: List[Path] = []

        def direct_visible_files(parent: QTreeWidgetItem) -> List[Path]:
            values: List[Path] = []
            if not parent.isExpanded():
                return values
            for child_index in range(parent.childCount()):
                child = parent.child(child_index)
                path = self.browser_item_path(child)
                if path and path.is_file():
                    values.append(path)
            return values

        def collect(parent: QTreeWidgetItem):
            if not parent.isExpanded():
                return
            group = direct_visible_files(parent)
            if group:
                groups.append(group)
            for child_index in range(parent.childCount()):
                child = parent.child(child_index)
                if self.browser_item_kind(child) in {"folder", "folder-child", "media-header", "media-ext-header"}:
                    collect(child)

        for top_index in range(self.table.topLevelItemCount()):
            top = self.table.topLevelItem(top_index)
            kind = self.browser_item_kind(top)
            path = self.browser_item_path(top)
            if path and path.is_file():
                top_direct.append(path)
            elif kind in {"folder", "folder-child", "media-header", "media-ext-header"}:
                collect(top)

        if top_direct:
            groups.insert(0, top_direct)
        return groups

    def toggle_numeration(self):
        if self.has_numbered_direct_files():
            self.denumerate_files()
        else:
            self.number_files_by_groups(self.visible_direct_file_groups_for_numbering(), "Numberate")

    def denumerate_files(self):
        folder = self.require_folder()
        if not folder:
            return

        if not self.confirm("Denumerate files", "This will remove leading order numbers from direct files."):
            return

        pairs: List[Tuple[Path, Path]] = []
        for file in self.visible_direct_file_paths():
            clean_name = strip_order_prefixes(file.name)
            dst = file.with_name(clean_name)
            if dst.name != file.name:
                pairs.append((file, dst))

        self.start_rename_operation("Denumerate", pairs)

    def order_by_media_types(self):
        self.media_grouped = not getattr(self, "media_grouped", False)
        self.update_sort_button_labels()
        self.reload_folder("Grouped by media type" if self.media_grouped else "Ungrouped")

    def open_duplicate_dialog(self):
        folder = self.require_folder()
        if not folder:
            return

        self.preview_panel.pause_video_preview()
        # Scanners own a recursive scope. Supplying visible rows here excluded
        # every collapsed folder before the worker had a chance to walk it.
        dialog = DuplicateDialog(folder, self, scan_files=None)
        dialog.setWindowModality(Qt.NonModal)
        dialog.setAttribute(Qt.WA_DeleteOnClose, True)
        self.duplicate_dialogs.append(dialog)
        dialog.finished.connect(lambda _result=0, d=dialog: self.remove_duplicate_dialog(d))
        dialog.destroyed.connect(lambda _obj=None, d=dialog: self.remove_duplicate_dialog(d))
        dialog.show()
        dialog.raise_()
        dialog.activateWindow()
        self.update_auxiliary_window_buttons()

    def remove_duplicate_dialog(self, dialog: DuplicateDialog):
        if dialog in self.duplicate_dialogs:
            self.duplicate_dialogs.remove(dialog)
        self.update_auxiliary_window_buttons()

    def open_bad_file_dialog(self):
        folder = self.require_folder()
        if not folder:
            return

        self.preview_panel.pause_video_preview()
        dialog = BadFileDialog(folder, self, scan_files=None)
        dialog.setWindowModality(Qt.NonModal)
        dialog.setAttribute(Qt.WA_DeleteOnClose, True)
        self.bad_file_dialogs.append(dialog)
        dialog.finished.connect(lambda _result=0, d=dialog: self.remove_bad_file_dialog(d))
        dialog.destroyed.connect(lambda _obj=None, d=dialog: self.remove_bad_file_dialog(d))
        dialog.show()
        dialog.raise_()
        dialog.activateWindow()
        self.update_auxiliary_window_buttons()

    def remove_bad_file_dialog(self, dialog: BadFileDialog):
        if dialog in self.bad_file_dialogs:
            self.bad_file_dialogs.remove(dialog)
        self.update_auxiliary_window_buttons()

    def zoom_browser_preview(self, path: Path):
        if not path or not path.exists() or path.is_dir():
            return
        self.table.preview_navigation_active = True
        created = self.quicklook_dialog is None
        if created:
            self.quicklook_dialog = LargePreviewDialog(
                self,
                self.preview_adjacent_browser_file,
                self.move_browser_selection_to_trash,
                self.preview_panel.cached_media_metadata_if_ready,
                self.current_browser_file_path,
                embedded_preview_panel=self.preview_panel,
            )
            self.quicklook_dialog.finished.connect(
                lambda _result=0: self.restore_browser_preview_after_quicklook()
            )
        self.quicklook_dialog.set_path(path)
        self.quicklook_dialog.show()
        self.quicklook_dialog.raise_()
        self.quicklook_dialog.activateWindow()
        debug_log(
            "response",
            "separate preview window opened",
            force=True,
            context="browser",
            created=created,
            media_kind=kind_for_path(path),
            width=self.quicklook_dialog.width(),
            height=self.quicklook_dialog.height(),
        )

    def close_child_windows(self):
        for dialog in list(self.duplicate_dialogs):
            try:
                if dialog.worker and dialog.worker.isRunning():
                    dialog.stop_scan()
                dialog.close()
            except RuntimeError:
                pass
        for dialog in list(self.bad_file_dialogs):
            try:
                if dialog.worker and dialog.worker.isRunning():
                    dialog.stop_scan()
                dialog.close()
            except RuntimeError:
                pass
        if self.quicklook_dialog and self.quicklook_dialog.isVisible():
            self.quicklook_dialog.close()

    def child_window_work_running(self) -> bool:
        dialogs = list(self.duplicate_dialogs) + list(self.bad_file_dialogs)
        for dialog in dialogs:
            try:
                if dialog.scan_thread_running() or dialog.trash_thread_running():
                    return True
            except RuntimeError:
                continue
        return False

    def retry_close_after_child_work(self):
        if not self.closing_after_child_work:
            return
        if self.child_window_work_running():
            QTimer.singleShot(200, self.retry_close_after_child_work)
            return
        self.closing_after_child_work = False
        self.close()

    def showEvent(self, event):
        super().showEvent(event)
        schedule_macos_native_fullscreen_button(self)

    def resizeEvent(self, event):
        super().resizeEvent(event)
        schedule_settled_window_geometry_remember(self)

    def moveEvent(self, event):
        super().moveEvent(event)
        schedule_settled_window_geometry_remember(self)

    def changeEvent(self, event):
        track_standard_fullscreen_change(self, event, "main")
        if promote_macos_zoom_to_fullscreen(
            self,
            event,
            before_promote=lambda: capture_standard_window_geometry(self, "main"),
        ):
            event.accept()
            return
        super().changeEvent(event)

    def closeEvent(self, event):
        debug_window_close_context(self, "main")
        if self.operation_worker and self.operation_worker.isRunning():
            self.closing_after_operation_cancel = True
            self.close_child_windows()
            self.status.setText("Closing: undoing current file operation")
            self.show_task_progress("Closing: undoing current file operation", 0)
            self.operation_worker.request_cancel()
            self.operation_worker.requestInterruption()
            event.ignore()
            return

        if self.has_active_trash_workers():
            self.closing_after_trash_moves = True
            self.close_child_windows()
            self.status.setText("Closing after the active Trash move finishes")
            for worker in list(self.trash_workers):
                try:
                    worker.requestInterruption()
                except RuntimeError:
                    pass
            event.ignore()
            return

        if self.table_populate_timer.isActive() or self.pending_table_entries:
            self.table_populate_timer.stop()
            self.pending_table_entries = []
            self.pending_table_total = 0
            self.pending_table_select_path = None
            self.pending_table_select_index = None
            self.table_reloading = False
            self.hide_task_progress()

        self.save_main_window_geometry()
        self.close_child_windows()
        if self.child_window_work_running():
            self.closing_after_child_work = True
            self.status.setText("Closing after scanner file work finishes")
            QTimer.singleShot(200, self.retry_close_after_child_work)
            event.ignore()
            return
        self.preview_panel.stop_preview_workers()
        self.folder_metric_cancel.set()
        try:
            self.folder_metric_executor.shutdown(wait=False, cancel_futures=True)
        except Exception:
            pass
        super().closeEvent(event)
        QTimer.singleShot(0, QApplication.quit)


def apply_app_style(app: QApplication):
    app.setStyleSheet(
        """
        QWidget {
            background-color: #2b2c31;
            color: #e4e4e8;
            selection-background-color: #5f6388;
            selection-color: #ffffff;
            font-size: 13px;
        }
        QMainWindow, QDialog { background-color: #2b2c31; }
        QDialog[cinema="true"],
        QStackedWidget#LargePreviewStack[cinema="true"],
        QLabel#LargePreviewPlaceholder[cinema="true"],
        QLabel#LargeImagePreview[cinema="true"],
        QTextEdit#LargeTextPreview[cinema="true"],
        FrameVideoWidget#LargeVideoPreview[cinema="true"] {
            background-color: #000000;
            border: none;
        }
        QLabel { background: transparent; color: #d9d9df; }
        QGroupBox {
            background-color: #33343a;
            color: #d7d7dd;
            border: 1px solid #484a52;
            border-radius: 8px;
            margin-top: 14px;
            padding: 4px 4px 4px 4px;
        }
        QGroupBox::title {
            subcontrol-origin: margin;
            subcontrol-position: top left;
            left: 8px;
            top: 2px;
            padding: 0px 5px;
            color: #c9cad2;
            background-color: #2b2c31;
        }
        QLabel#AppTitle {
            color: #f0f0f4;
            font-size: 18px;
            font-weight: 700;
        }
        QLabel#PathLabel, QLabel#MutedLabel {
            color: #a8a9b2;
        }
        QWidget#BreadcrumbPath {
            background: transparent;
        }
        QLabel#BreadcrumbSegment {
            color: #a8a9b2;
            padding: 0px;
        }
        QLabel#BreadcrumbSegment:hover {
            color: #f0f0f4;
            text-decoration: underline;
        }
        QLabel#BreadcrumbSeparator, QLabel#BreadcrumbMuted {
            color: #a8a9b2;
            padding: 0px;
        }
        QLabel#SectionTitle {
            color: #f0f0f4;
            font-size: 14px;
            font-weight: 700;
        }
        QWidget#PreviewChrome[cinema="true"] {
            background: transparent;
            border: none;
            border-radius: 0px;
        }
        QWidget#CinemaChromeLayer {
            background: transparent;
            border: none;
        }
        QLabel#SectionTitle[cinema="true"],
        QLabel#MutedLabel[cinema="true"] {
            color: #ffffff;
            background: transparent;
        }
        QPushButton[cinema="true"] {
            background-color: transparent;
            color: #ffffff;
            border: none;
            border-radius: 0px;
            font-weight: 600;
        }
        QPushButton[cinema="true"]:hover {
            background-color: rgba(255, 255, 255, 18);
            border: none;
        }
        QSlider#PreviewScrubSlider[cinema="true"] {
            background: transparent;
            border: none;
        }
        QSlider#PreviewScrubSlider[cinema="true"]::groove:horizontal {
            height: 4px;
            background: rgba(255, 255, 255, 55);
            border: none;
            border-radius: 2px;
        }
        QSlider#PreviewScrubSlider[cinema="true"]::handle:horizontal {
            width: 12px;
            height: 12px;
            margin: -4px 0px;
            border-radius: 6px;
            background: #ffffff;
            border: none;
        }
        QSlider#PreviewScrubSlider[cinema="true"]::sub-page:horizontal {
            background: rgba(255, 255, 255, 180);
            border: none;
            border-radius: 2px;
        }
        QLabel#MetricTitle {
            color: #aeb0ba;
            font-size: 12px;
            font-weight: 600;
        }
        QLabel#MetricValue {
            color: #f4f4f6;
            font-size: 20px;
            font-weight: 700;
        }
        QLabel#MetricMeta {
            color: #9ea0aa;
            font-size: 12px;
        }
        QLabel#DetailLabel {
            color: #a9abb4;
            font-weight: 700;
        }
        QLabel#DetailValue {
            color: #e4e4e8;
        }
        QLabel#PreviewTitle {
            color: #f0f0f4;
            font-weight: 700;
        }
        QWidget#PreviewInfoPanel, QWidget#PreviewMediaPanel {
            background: transparent;
            border: none;
        }
        FrameVideoWidget#VideoPreview {
            background-color: #000000;
            border: 1px solid #4b4d55;
            border-radius: 6px;
        }
        QLabel#ThumbnailPreview {
            border: 1px solid #4b4d55;
            border-radius: 6px;
            background: #000000;
            color: #d8d9df;
        }
        QLabel#DropBox {
            background-color: #303139;
            color: #dfe0e6;
            border: 1px dashed #696c78;
            border-radius: 8px;
            font-size: 15px;
            font-weight: 600;
        }
        QLabel#DropBox:hover {
            border-color: #8f98c8;
            background-color: #33343c;
        }
        QFrame#MetricCard, QWidget#Inspector {
            background-color: #33343a;
            border: 1px solid #484a52;
            border-radius: 8px;
        }
        QSplitter::handle {
            background-color: #2b2c31;
            width: 8px;
        }
        QPushButton {
            background-color: #3f4149;
            color: #ececf0;
            border: 1px solid #585a64;
            border-radius: 7px;
            padding: 5px 12px;
        }
        QPushButton:hover { background-color: #494b54; border-color: #686b75; }
        QPushButton:pressed { background-color: #363841; }
        QPushButton:disabled {
            background-color: #303138;
            color: #858690;
            border-color: #42444b;
        }
        QPushButton#BrightGreyButton {
            background-color: #70737c;
            color: #ffffff;
            border: 1px solid #8d909a;
            font-weight: 600;
        }
        QPushButton#BrightGreyButton:hover {
            background-color: #828691;
            border-color: #b5bac6;
        }
        QPushButton#BrightGreyButton:pressed {
            background-color: #62656e;
        }
        QPushButton#BrightGreyButton:disabled {
            background-color: #303138;
            color: #858690;
            border-color: #42444b;
        }
        QTableWidget, QTreeWidget {
            background-color: #25262c;
            alternate-background-color: #2a2b31;
            color: #ededf2;
            border: 1px solid #50525b;
            border-radius: 4px;
            gridline-color: #3e4048;
        }
        QTableWidget::item, QTreeWidget::item {
            padding: 4px 7px;
            border: none;
        }
        QTableWidget::item:selected, QTreeWidget::item:selected {
            background-color: #626b7f;
            color: #ffffff;
        }
        QHeaderView::section {
            background-color: #3b3c43;
            color: #e2e2e7;
            border: none;
            border-right: 1px solid #565862;
            border-bottom: 1px solid #565862;
            padding: 5px 7px;
            font-weight: 700;
        }
        QTableCornerButton::section {
            background-color: #3b3c43;
            border: none;
            border-right: 1px solid #565862;
            border-bottom: 1px solid #565862;
        }
        QProgressBar {
            background-color: #26272d;
            color: #f1f1f4;
            border: 1px solid #555761;
            border-radius: 6px;
            text-align: center;
            min-height: 12px;
        }
        QProgressBar::chunk {
            background-color: #9b99cf;
            border-radius: 5px;
        }
        QSlider#PreviewScrubSlider {
            background: transparent;
            border: none;
        }
        QSlider#PreviewScrubSlider::groove:horizontal {
            height: 5px;
            background: #4b4d55;
            border-radius: 3px;
        }
        QSlider#PreviewScrubSlider::handle:horizontal {
            width: 12px;
            height: 12px;
            margin: -4px 0px;
            border-radius: 6px;
            background: #d4d5dd;
            border: 1px solid #777985;
        }
        QSlider#PreviewScrubSlider::sub-page:horizontal {
            background: #8f98c8;
            border-radius: 3px;
        }
        QToolButton#PreviewMuteButton {
            background-color: #3f4149;
            color: #ececf0;
            border: 1px solid #585a64;
            border-radius: 5px;
            font-size: 11px;
            font-weight: 700;
            padding: 0px;
        }
        QToolButton#PreviewMuteButton:hover {
            background-color: #494b54;
            border-color: #686b75;
        }
        QToolButton#UndoButton {
            background-color: #3f4149;
            border: 1px solid #585a64;
            border-radius: 7px;
            padding: 0px;
        }
        QToolButton#UndoButton:hover {
            background-color: #494b54;
            border-color: #686b75;
        }
        QToolButton#UndoButton:disabled {
            background-color: #303138;
            border-color: #42444b;
        }
        QScrollBar:vertical, QScrollBar:horizontal {
            background: #2b2c31;
            border: none;
            margin: 0px;
        }
        QScrollBar::handle:vertical, QScrollBar::handle:horizontal {
            background: #5b5d66;
            border-radius: 5px;
            min-height: 24px;
            min-width: 24px;
        }
        QScrollBar::handle:vertical:hover, QScrollBar::handle:horizontal:hover {
            background: #70727c;
        }
        QScrollBar::add-line, QScrollBar::sub-line,
        QScrollBar::add-page, QScrollBar::sub-page {
            border: none;
            background: transparent;
            width: 0px;
            height: 0px;
        }
        """
    )

    palette = app.palette()
    palette.setColor(palette.ColorRole.Window, QColor("#2b2c31"))
    palette.setColor(palette.ColorRole.WindowText, QColor("#e4e4e8"))
    app.setPalette(palette)


def schedule_frozen_smoke_exit(app: QApplication) -> bool:
    # Frozen-build smoke tests run without a macOS login-window connection.
    # Give them a graceful Qt exit path so validation never needs SIGQUIT/SIGTERM.
    smoke_exit_ms = os.environ.get("FOLDER_MANAGER_SMOKE_EXIT_MS", "").strip()
    if not smoke_exit_ms:
        return False
    try:
        QTimer.singleShot(max(50, min(60_000, int(smoke_exit_ms))), app.quit)
        return True
    except ValueError:
        debug_log("startup", "ignored invalid smoke exit interval")
        return False


def main():
    app = QApplication(sys.argv)
    load_previous_watchdog_diagnostics()
    start_application_watchdog(app)
    # Connect this before constructing any window so the global worker drain runs
    # before per-widget teardown and before PySide destroys QThread wrappers.
    app.aboutToQuit.connect(stop_application_watchdog)
    app.aboutToQuit.connect(drain_preview_workers)
    app.aboutToQuit.connect(drain_scan_workers)
    apply_app_style(app)
    if schedule_packaged_media_smoke(app):
        # Release validation decodes a real video through the frozen bundle.
        # Avoid constructing the browser so this result measures multimedia
        # packaging rather than unrelated startup work.
        sys.exit(app.exec())
    window = FolderManager()
    window.show()
    schedule_frozen_smoke_exit(app)
    sys.exit(app.exec())


if __name__ == "__main__":
    main()
