#!/usr/bin/env python3
# SHARED MEDIA VERSION: v1.0.54 (used by Folder Manager and Delta Downloader)

"""Shared media toolkit used by Folder Manager and Delta Downloader.

Version: v1.0.54

The module is organized as four layers: shared runtime identity and diagnostics,
media probing/preview infrastructure, reusable file-browser models and widgets,
and the duplicate/bad-file scanner dialogs.  Application-specific navigation
and download logic remain in their application modules.  This module is imported;
it is not a standalone application entry point.
"""

from __future__ import annotations

import atexit
import bz2
import concurrent.futures
import bisect
import gzip
import hashlib
import io
import json
import mimetypes
import lzma
import os
import queue
import re
import shutil
import stat as stat_module
import subprocess
import sys
import tempfile
import tarfile
import threading
import time
import traceback
import uuid
import weakref
import xml.etree.ElementTree as ET
import zipfile
from collections import Counter, defaultdict, deque
from dataclasses import dataclass
from datetime import datetime
from functools import lru_cache
from pathlib import Path
from typing import Callable, Dict, Iterable, List, Optional, Sequence, Tuple


# IMPORTANT: Qt Multimedia reads its FFmpeg backend/hardware-decoder environment
# during Qt/PySide initialization. These must be set before importing *any*
# PySide6 module, not merely before importing PySide6.QtMultimedia.
os.environ.setdefault("QT_MEDIA_BACKEND", "ffmpeg")
if sys.platform == "darwin" and os.environ.get("FM_ALLOW_QT_HW_DECODING", "").strip().lower() not in {"1", "true", "yes"}:
    # Qt's documented empty-list syntax disables all FFmpeg hardware decoders.
    # This prevents VideoToolbox from being selected for AV1 on Macs where that
    # path advertises itself but cannot actually provide frames.
    os.environ["QT_FFMPEG_DECODING_HW_DEVICE_TYPES"] = ","
    # Keep frame conversion on the CPU too; this avoids a second GPU-only path
    # from turning a successfully software-decoded frame into a blank preview.
    os.environ["QT_DISABLE_HW_TEXTURES_CONVERSION"] = "1"

from PySide6.QtCore import (
    QEasingCurve,
    QEvent,
    QMimeData,
    QObject,
    QModelIndex,
    QPersistentModelIndex,
    QPropertyAnimation,
    QPoint,
    QRect,
    QSize,
    QSettings,
    Qt,
    QThread,
    QTimer,
    QUrl,
    Signal,
    QtMsgType,
    qInstallMessageHandler,
    qVersion,
)
from PySide6.QtGui import (
    QBrush,
    QColor,
    QCursor,
    QDragEnterEvent,
    QDropEvent,
    QKeySequence,
    QPainter,
    QPen,
    QPixmap,
    QRegion,
    QShortcut,
)
from PySide6.QtWidgets import (
    QApplication,
    QAbstractButton,
    QAbstractItemView,
    QAbstractSlider,
    QComboBox,
    QDialog,
    QFileDialog,
    QFrame,
    QGraphicsOpacityEffect,
    QGridLayout,
    QGroupBox,
    QHBoxLayout,
    QHeaderView,
    QLabel,
    QLineEdit,
    QMenu,
    QMessageBox,
    QProgressBar,
    QPushButton,
    QPlainTextEdit,
    QToolButton,
    QSizePolicy,
    QSlider,
    QStackedWidget,
    QStyledItemDelegate,
    QTableWidgetItem,
    QTabBar,
    QTextEdit,
    QTreeWidget,
    QTreeWidgetItem,
    QVBoxLayout,
    QWidget,
)

try:
    from PySide6.QtMultimedia import QAudioOutput, QMediaDevices, QMediaPlayer, QVideoSink
    try:
        # Qt 6.8+ can expose decoded audio buffers while it also sends sound to
        # QAudioOutput.  The monitor below uses this as positive evidence that
        # a preview decoded audio instead of merely trusting hasAudio().
        from PySide6.QtMultimedia import QAudioBufferOutput
    except Exception:
        QAudioBufferOutput = None
    from PySide6.QtMultimediaWidgets import QVideoWidget

    MEDIA_PREVIEW_AVAILABLE = True
except Exception:
    QAudioOutput = None
    QAudioBufferOutput = None
    QMediaDevices = None
    QMediaPlayer = None
    QVideoSink = None
    QVideoWidget = None
    MEDIA_PREVIEW_AVAILABLE = False

# NumPy/OpenBLAS can be pulled in by optional media similarity libraries.
# Keep it single-threaded when launched from this app; it is safer inside Qt workers.
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("OMP_NUM_THREADS", "1")

APP_TITLE = "Folder Manager"
APP_VERSION = "v1.0.54"
WINDOW_TRACE_BUILD_ID = "FM-PREVIEW-STABLE-20260907-A"
APP_DISPLAY_TITLE = f"{APP_TITLE} {APP_VERSION}"
SETTINGS_ORG = "FolderManager"
SETTINGS_APP = "Folder Manager"
PREVIEW_CANVAS_COLOR = "#000000"
PAUSED_OVERLAY_STYLE = (
    "color: #ffffff; background-color: rgba(0, 0, 0, 105); "
    "border: none; border-radius: 6px; padding: 2px 10px; "
    "font-size: 15px; font-weight: 700;"
)


# ---------------------------------------------------------------------------
# Shared application identity

DEBUG_WINDOW_TITLE = "Folder Manager Debug"
DIAGNOSTIC_FOLDER = "Folder Manager"


def configure_shared_runtime(
    *,
    settings_org: str,
    settings_app: str,
    debug_window_title: str,
    diagnostic_folder: str,
):
    """Configure the small amount of app identity used by shared UI code.

    Both applications execute the exact same classes.  Only their settings and
    diagnostic namespaces differ.  This function must be called before either
    app creates a shared window or starts its watchdog.
    """
    global SETTINGS_ORG, SETTINGS_APP, DEBUG_WINDOW_TITLE, DIAGNOSTIC_FOLDER
    SETTINGS_ORG = str(settings_org)
    SETTINGS_APP = str(settings_app)
    DEBUG_WINDOW_TITLE = str(debug_window_title)
    DIAGNOSTIC_FOLDER = str(diagnostic_folder)

VIDEO_PLAYBACK_OWNERS: List[object] = []
DEBUG_LINES: List[str] = []
DEBUG_WINDOW = None
DEBUG_LAST_STATE: Dict[object, Tuple[Tuple[Tuple[str, str], ...], float]] = {}
DEBUG_RATE_LAST: Dict[object, float] = {}
DEBUG_LOCK = threading.RLock()
PERSISTENT_DIAGNOSTIC_LOCK = threading.Lock()
PERSISTENT_DIAGNOSTIC_START_LOCK = threading.Lock()
PERSISTENT_DIAGNOSTIC_DROP_LOCK = threading.Lock()
PERSISTENT_DIAGNOSTIC_QUEUE_LIMIT = 2048
PERSISTENT_DIAGNOSTIC_QUEUE: "queue.Queue[str]" = queue.Queue(
    maxsize=PERSISTENT_DIAGNOSTIC_QUEUE_LIMIT
)
PERSISTENT_DIAGNOSTIC_THREAD: Optional[threading.Thread] = None
PERSISTENT_DIAGNOSTIC_DROPPED = 0
DEBUG_LINE_LIMIT = 2000
# Detailed per-input snapshots are for a reproduction session, not daily use.
VERBOSE_INTERACTION_DIAGNOSTICS = os.environ.get("MEDIA_PREVIEW_TRACE_INPUT", "").lower() in {"1", "true", "yes"}
DEBUG_STATE_LIMIT = 1024
PREVIEW_DEBUG_SOURCE_PREFIXES = ("media-preview", "media-proxy", "preview-qt")
ROUTINE_PREVIEW_LOG_INTERVALS = {
    "Qt media capabilities changed": 0.25,
    "Qt media status changed": 0.12,
    "Qt playback state changed": 0.12,
    "seek backend suppressed stale backend position": 0.40,
}
QT_MEDIA_MESSAGE_COUNTS: Dict[Tuple[str, str], Tuple[int, float]] = {}
QT_MEDIA_MESSAGE_LOCK = threading.Lock()
QT_MEDIA_PENDING_MESSAGES: deque = deque()
QT_MEDIA_MESSAGE_TIMER = None
QT_MEDIA_MESSAGE_HANDLER_INSTALLED = False
QT_PREVIOUS_MESSAGE_HANDLER = None
ACTIVE_PREVIEW_WORKERS: set = set()
ACTIVE_PREVIEW_WORKERS_LOCK = threading.Lock()
PREVIEW_CACHE_KEY_LOCKS: Dict[str, List[object]] = {}
PREVIEW_CACHE_KEY_LOCKS_GUARD = threading.Lock()
PREVIEW_CACHE_MAINTENANCE_LOCK = threading.Lock()
PREVIEW_CACHE_LAST_MAINTENANCE: Dict[str, float] = {}
# Successful proxy validation is expensive (one source probe plus video/audio
# probes and decodes).  A completed proxy is immutable, so share positive
# results between the embedded and large-preview workers.  Source and proxy
# identities make an in-place mutation an automatic cache miss.
PREVIEW_PROXY_VALIDATION_CACHE: Dict[Tuple[object, ...], float] = {}
PREVIEW_PROXY_VALIDATION_CACHE_LOCK = threading.Lock()
PREVIEW_PROXY_VALIDATION_CACHE_LIMIT = 256
ACTIVE_SCAN_WORKERS: set = set()
ACTIVE_SCAN_WORKERS_LOCK = threading.Lock()
ACTIVE_SCAN_STATE: Dict[int, Dict[str, object]] = {}
APP_WATCHDOG_STOP = threading.Event()
APP_WATCHDOG_THREAD: Optional[threading.Thread] = None
APP_WATCHDOG_HEARTBEAT = None
GUI_HEARTBEAT_LOCK = threading.Lock()
GUI_HEARTBEAT_AT = time.monotonic()
GUI_HEARTBEAT_ACTIVE = True
FINGERPRINT_DIAGNOSTICS = Counter()
FINGERPRINT_DIAGNOSTICS_LOCK = threading.Lock()
# The coarse pass uses three seekable FFmpeg inputs. Eight concurrent jobs was
# consistently faster than four on the target M1 Max/external-SSD library, but
# keep the limit process-wide so two open scanners cannot multiply that load.
SCAN_MEDIA_WORKERS = max(1, min(8, os.cpu_count() or 8))
# A bad-file check now decodes complete streams. Four two-thread decoders keep
# the GUI responsive and avoid the eight-process saturation seen in watchdog
# diagnostics, while Duplicate Scan may still use the broader shared limit.
BAD_FILE_SCAN_WORKERS = max(1, min(4, os.cpu_count() or 4))
# Scanner result widgets share Qt's GUI thread with video-frame presentation.
# Keep each result insertion turn below half of a 60 Hz frame; the remaining
# rows are delivered by the existing single-shot timers on later turns.
SCANNER_RESULT_BATCH_ROWS = 24
SCANNER_GUI_SLICE_SECONDS = 0.006
VIDEO_FINGERPRINT_SLOTS = threading.BoundedSemaphore(SCAN_MEDIA_WORKERS)
VIDEO_FINGERPRINT_CACHE: Dict[Tuple[object, ...], "VideoFingerprint"] = {}
VIDEO_FINGERPRINT_INFLIGHT: Dict[Tuple[object, ...], concurrent.futures.Future] = {}
VIDEO_FINGERPRINT_CACHE_LOCK = threading.Lock()
VIDEO_FINGERPRINT_CACHE_LIMIT = 12000


# ---------------------------------------------------------------------------
# Preview and scanner worker lifetime


class PreviewWorkerCancelled(Exception):
    pass


def preview_file_identity(path: Path) -> Optional[Tuple[object, ...]]:
    """Identity used by preview caches, including same-size in-place rewrites."""
    try:
        st = path.stat()
        return (
            str(path.resolve()),
            int(getattr(st, "st_dev", 0)),
            int(getattr(st, "st_ino", 0)),
            int(st.st_size),
            int(getattr(st, "st_mtime_ns", int(st.st_mtime * 1_000_000_000))),
            int(getattr(st, "st_ctime_ns", int(st.st_ctime * 1_000_000_000))),
        )
    except OSError:
        return None


class PreviewCacheKeySlot:
    """Serialize poster generation for one file without blocking unrelated files."""

    def __init__(self, key: str, worker: "PreviewProcessWorker"):
        self.key = key
        self.worker = worker
        self.entry: Optional[List[object]] = None
        self.acquired = False

    def __enter__(self):
        with PREVIEW_CACHE_KEY_LOCKS_GUARD:
            entry = PREVIEW_CACHE_KEY_LOCKS.get(self.key)
            if entry is None:
                entry = [threading.Lock(), 0]
                PREVIEW_CACHE_KEY_LOCKS[self.key] = entry
            entry[1] = int(entry[1]) + 1
            self.entry = entry
        lock = entry[0]
        try:
            while not lock.acquire(timeout=0.05):
                if self.worker.isInterruptionRequested():
                    raise PreviewWorkerCancelled()
            self.acquired = True
            if self.worker.isInterruptionRequested():
                raise PreviewWorkerCancelled()
            return self
        except Exception:
            self._release_reference()
            raise

    def _release_reference(self):
        entry = self.entry
        if entry is None:
            return
        if self.acquired:
            entry[0].release()
            self.acquired = False
        with PREVIEW_CACHE_KEY_LOCKS_GUARD:
            entry[1] = max(0, int(entry[1]) - 1)
            if entry[1] == 0 and PREVIEW_CACHE_KEY_LOCKS.get(self.key) is entry:
                PREVIEW_CACHE_KEY_LOCKS.pop(self.key, None)
        self.entry = None

    def __exit__(self, exc_type, exc_value, exc_traceback):
        self._release_reference()


def maintain_preview_cache(
    cache_dir: Path,
    *,
    suffix: object = ".jpg",
    max_files: int = 512,
    keep_files: int = 400,
    max_bytes: int = 512 * 1024 * 1024,
    max_age_seconds: float = 14 * 24 * 60 * 60,
):
    """Bound a preview cache without rescanning it for every row selection.

    Poster JPEGs and playable video proxies share the same maintenance code but
    use different limits.  Entries are evicted oldest-first by both age and
    aggregate bytes; abandoned hidden temporary/lock files are also removed.
    """
    now = time.monotonic()
    cache_key = os.path.normcase(os.path.abspath(os.fspath(cache_dir)))
    last_maintenance = float(PREVIEW_CACHE_LAST_MAINTENANCE.get(cache_key, 0.0) or 0.0)
    if now - last_maintenance < 60.0:
        return
    if not PREVIEW_CACHE_MAINTENANCE_LOCK.acquire(blocking=False):
        return
    try:
        now = time.monotonic()
        last_maintenance = float(PREVIEW_CACHE_LAST_MAINTENANCE.get(cache_key, 0.0) or 0.0)
        if now - last_maintenance < 60.0:
            return
        try:
            wall_now = time.time()
            suffixes = (
                {str(value).casefold() for value in suffix}
                if isinstance(suffix, (tuple, list, set, frozenset))
                else {str(suffix).casefold()}
            )
            entries: List[Tuple[float, int, Path]] = []
            for candidate in cache_dir.iterdir():
                if not candidate.is_file():
                    continue
                try:
                    stat = candidate.stat()
                except OSError:
                    continue
                if candidate.name.startswith("."):
                    if wall_now - float(stat.st_mtime) > 24 * 60 * 60:
                        candidate.unlink(missing_ok=True)
                    continue
                if candidate.suffix.casefold() not in suffixes:
                    continue
                if wall_now - float(stat.st_mtime) > max_age_seconds:
                    candidate.unlink(missing_ok=True)
                    continue
                entries.append((float(stat.st_mtime), max(0, int(stat.st_size)), candidate))

            entries.sort(key=lambda value: value[0])
            total_bytes = sum(value[1] for value in entries)
            target_count = max(0, min(int(keep_files), int(max_files)))
            while entries and (
                len(entries) > int(max_files)
                or total_bytes > int(max_bytes)
            ):
                _modified, size, stale = entries.pop(0)
                stale.unlink(missing_ok=True)
                total_bytes = max(0, total_bytes - size)
            while len(entries) > target_count:
                _modified, size, stale = entries.pop(0)
                stale.unlink(missing_ok=True)
                total_bytes = max(0, total_bytes - size)
        except OSError:
            pass
        PREVIEW_CACHE_LAST_MAINTENANCE[cache_key] = now
    finally:
        PREVIEW_CACHE_MAINTENANCE_LOCK.release()


class ScanCancelled(Exception):
    pass


class FolderMetricCancelled(Exception):
    pass


SCAN_SUBPROCESS_CONTEXT = threading.local()
ACTIVE_SCAN_PROCESSES: Dict[int, set] = defaultdict(set)
ACTIVE_SCAN_PROCESSES_LOCK = threading.Lock()


def stop_child_process(process: subprocess.Popen):
    """Stop a scanner/preview child without waiting for its normal timeout."""
    if process.poll() is not None:
        return
    try:
        process.terminate()
        process.wait(timeout=0.35)
    except subprocess.TimeoutExpired:
        try:
            process.kill()
            process.wait(timeout=1.0)
        except Exception:
            pass
    except (OSError, ProcessLookupError):
        pass


def close_child_process_streams(process: subprocess.Popen):
    for stream_name in ("stdin", "stdout", "stderr"):
        stream = getattr(process, stream_name, None)
        if stream is None:
            continue
        try:
            stream.close()
        except (OSError, ValueError):
            pass


def scan_worker_cancelled(worker=None) -> bool:
    worker = worker or getattr(SCAN_SUBPROCESS_CONTEXT, "worker", None)
    if worker is None:
        return False
    try:
        return bool(getattr(worker, "_cancel_requested", False) or worker.isInterruptionRequested())
    except RuntimeError:
        return True


def raise_if_scan_cancelled(worker=None):
    if scan_worker_cancelled(worker):
        raise ScanCancelled()


def run_scan_task(worker, function: Callable, *args, **kwargs):
    """Propagate scanner ownership into executor threads."""
    missing = object()
    previous = getattr(SCAN_SUBPROCESS_CONTEXT, "worker", missing)
    SCAN_SUBPROCESS_CONTEXT.worker = worker
    try:
        raise_if_scan_cancelled(worker)
        return function(*args, **kwargs)
    finally:
        if previous is missing:
            try:
                del SCAN_SUBPROCESS_CONTEXT.worker
            except AttributeError:
                pass
        else:
            SCAN_SUBPROCESS_CONTEXT.worker = previous


def cancel_scan_processes(worker):
    worker_id = id(worker)
    with ACTIVE_SCAN_PROCESSES_LOCK:
        processes = list(ACTIVE_SCAN_PROCESSES.get(worker_id, ()))
    for process in processes:
        stop_child_process(process)


def scan_subprocess_run(
    command,
    *,
    timeout: Optional[float] = None,
    text: bool = False,
    capture_output: bool = False,
    stdout=None,
    stderr=None,
    input=None,
    check: bool = False,
    **kwargs,
) -> subprocess.CompletedProcess:
    """A subprocess.run-compatible runner cancellable by the owning scanner."""
    worker = getattr(SCAN_SUBPROCESS_CONTEXT, "worker", None)
    if worker is None:
        return subprocess.run(
            command,
            timeout=timeout,
            text=text,
            capture_output=capture_output,
            stdout=stdout,
            stderr=stderr,
            input=input,
            check=check,
            **kwargs,
        )

    raise_if_scan_cancelled(worker)
    if capture_output:
        if stdout is not None or stderr is not None:
            raise ValueError("stdout and stderr may not be used with capture_output")
        stdout = subprocess.PIPE
        stderr = subprocess.PIPE
    if input is not None:
        if kwargs.get("stdin") is not None:
            raise ValueError("stdin and input arguments may not both be used")
        kwargs["stdin"] = subprocess.PIPE

    process = subprocess.Popen(
        command,
        text=text,
        stdout=stdout,
        stderr=stderr,
        **kwargs,
    )
    worker_id = id(worker)
    with ACTIVE_SCAN_PROCESSES_LOCK:
        ACTIVE_SCAN_PROCESSES[worker_id].add(process)

    deadline = time.monotonic() + timeout if timeout is not None else None
    process_input = input
    try:
        while True:
            if scan_worker_cancelled(worker):
                stop_child_process(process)
                raise ScanCancelled()
            wait_slice = 0.1
            if deadline is not None:
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    stop_child_process(process)
                    raise subprocess.TimeoutExpired(command, timeout)
                wait_slice = min(wait_slice, remaining)
            try:
                process_stdout, process_stderr = process.communicate(
                    input=process_input,
                    timeout=wait_slice,
                )
                raise_if_scan_cancelled(worker)
                result = subprocess.CompletedProcess(
                    command,
                    process.returncode,
                    process_stdout,
                    process_stderr,
                )
                if check and result.returncode:
                    raise subprocess.CalledProcessError(
                        result.returncode,
                        command,
                        output=result.stdout,
                        stderr=result.stderr,
                    )
                return result
            except subprocess.TimeoutExpired:
                process_input = None
    finally:
        with ACTIVE_SCAN_PROCESSES_LOCK:
            owned = ACTIVE_SCAN_PROCESSES.get(worker_id)
            if owned is not None:
                owned.discard(process)
                if not owned:
                    ACTIVE_SCAN_PROCESSES.pop(worker_id, None)
        close_child_process_streams(process)


def wait_for_scan_future(future: concurrent.futures.Future, timeout: Optional[float] = None):
    deadline = time.monotonic() + timeout if timeout is not None else None
    while True:
        raise_if_scan_cancelled()
        wait_slice = 0.1
        if deadline is not None:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise concurrent.futures.TimeoutError()
            wait_slice = min(wait_slice, remaining)
        try:
            return future.result(timeout=wait_slice)
        except concurrent.futures.TimeoutError:
            continue


class ScanMediaSlot:
    def __init__(self):
        self.acquired = False

    def __enter__(self):
        while not VIDEO_FINGERPRINT_SLOTS.acquire(timeout=0.1):
            raise_if_scan_cancelled()
        self.acquired = True
        try:
            raise_if_scan_cancelled()
        except Exception:
            VIDEO_FINGERPRINT_SLOTS.release()
            self.acquired = False
            raise
        return self

    def __exit__(self, exc_type, exc_value, exc_traceback):
        if self.acquired:
            VIDEO_FINGERPRINT_SLOTS.release()
            self.acquired = False


class PreviewProcessWorker(QThread):
    """QThread with a child process that can be stopped cleanly during Qt teardown."""

    def __init__(self):
        super().__init__()
        self._process_lock = threading.Lock()
        self._process: Optional[subprocess.Popen] = None
        with ACTIVE_PREVIEW_WORKERS_LOCK:
            ACTIVE_PREVIEW_WORKERS.add(self)
        self.finished.connect(self._unregister)

    def _unregister(self):
        with ACTIVE_PREVIEW_WORKERS_LOCK:
            ACTIVE_PREVIEW_WORKERS.discard(self)

    @staticmethod
    def _stop_process(process: subprocess.Popen):
        stop_child_process(process)

    def cancel(self):
        """Request cancellation without ever waiting on a child in the caller.

        Selection changes and slider/key navigation call this method from
        Qt's GUI thread.  Terminating and waiting here used to freeze input for
        up to 1.35 seconds per superseded preview.  The worker's polling loop
        observes the interruption within its short wait slice and owns child
        termination, killing, stream cleanup, and reaping.
        """
        self.requestInterruption()

    def run_subprocess(
        self,
        command,
        *,
        timeout: Optional[float] = None,
        text: bool = False,
        capture_output: bool = False,
        stdout=None,
        stderr=None,
        **kwargs,
    ) -> subprocess.CompletedProcess:
        if self.isInterruptionRequested():
            raise PreviewWorkerCancelled()
        if capture_output:
            if stdout is not None or stderr is not None:
                raise ValueError("stdout and stderr may not be used with capture_output")
            stdout = subprocess.PIPE
            stderr = subprocess.PIPE

        process = subprocess.Popen(
            command,
            text=text,
            stdout=stdout,
            stderr=stderr,
            **kwargs,
        )
        with self._process_lock:
            self._process = process

        deadline = time.monotonic() + timeout if timeout is not None else None
        try:
            while True:
                if self.isInterruptionRequested():
                    self._stop_process(process)
                    raise PreviewWorkerCancelled()
                wait_slice = 0.1
                if deadline is not None:
                    remaining = deadline - time.monotonic()
                    if remaining <= 0:
                        self._stop_process(process)
                        raise subprocess.TimeoutExpired(command, timeout)
                    wait_slice = min(wait_slice, remaining)
                try:
                    process_stdout, process_stderr = process.communicate(timeout=wait_slice)
                    result = subprocess.CompletedProcess(
                        command,
                        process.returncode,
                        process_stdout,
                        process_stderr,
                    )
                    # Cancellation can race the last communicate()/waitpid.
                    # Never let a user-cancelled subprocess look like an
                    # encoder/probe failure merely because it exited first.
                    if self.isInterruptionRequested():
                        raise PreviewWorkerCancelled()
                    return result
                except subprocess.TimeoutExpired:
                    continue
        finally:
            with self._process_lock:
                if self._process is process:
                    self._process = None
            close_child_process_streams(process)

    def execute(self):
        raise NotImplementedError

    def run(self):
        try:
            self.execute()
        except PreviewWorkerCancelled:
            pass


def stop_preview_worker_collection(
    workers: List[PreviewProcessWorker],
    *,
    wait_for_exit: bool = True,
):
    snapshot = list(dict.fromkeys(workers))
    for worker in snapshot:
        try:
            worker.cancel()
        except RuntimeError:
            pass
    workers.clear()
    if not wait_for_exit:
        # ACTIVE_PREVIEW_WORKERS and the finished callbacks retain both the
        # worker and its receiver until a slow filesystem/Pillow call returns.
        return

    deadline = time.monotonic() + 3.0
    for worker in snapshot:
        try:
            remaining_ms = max(0, int((deadline - time.monotonic()) * 1000))
            if worker.isRunning() and remaining_ms:
                worker.wait(remaining_ms)
        except RuntimeError:
            pass
    for worker in snapshot:
        try:
            if worker.isRunning():
                # Only used during final application teardown. A dead external
                # volume must not leave a live QThread wrapper that aborts Qt.
                worker.terminate()
                worker.wait(1000)
        except RuntimeError:
            pass


def preview_proxy_running(workers: Iterable[object], path: Path) -> bool:
    """Return whether the same compatibility conversion is already active."""
    for worker in list(workers):
        if getattr(worker, "path", None) != path:
            continue
        try:
            # A cancelled QThread remains ``isRunning()`` briefly while its
            # subprocess unwinds. Treating it as reusable creates an A -> B -> A
            # navigation race: the replacement A worker is skipped, then the
            # cancelled worker exits without ever publishing a source.
            if worker.isRunning() and not worker.isInterruptionRequested():
                return True
        except RuntimeError:
            continue
    return False


def drain_preview_workers():
    with ACTIVE_PREVIEW_WORKERS_LOCK:
        workers = list(ACTIVE_PREVIEW_WORKERS)
    stop_preview_worker_collection(workers)


def schedule_packaged_media_smoke(app: QApplication) -> bool:
    """Exercise the real preview recovery path inside a frozen application.

    ``SHARED_MEDIA_SMOKE_PATH`` is intentionally test-only.  A raw
    ``QMediaPlayer`` check cannot validate the application: on macOS Qt can
    claim that AV1 is Playing/Buffered while delivering audio and zero video
    frames.  The smoke run therefore uses ``PreviewPanel`` itself, including
    its codec-aware compatibility proxy, and succeeds only after the ordinary
    frame-painting widget has retained a convertible image.
    """
    media_path = os.environ.get("SHARED_MEDIA_SMOKE_PATH", "").strip()
    if not media_path:
        return False
    path = Path(media_path).expanduser()
    if not path.is_file() or not MEDIA_PREVIEW_AVAILABLE:
        QTimer.singleShot(0, lambda: app.exit(41))
        return True

    panel = PreviewPanel(compact=True)
    panel.resize(620, 220)
    panel.show()
    require_audio = os.environ.get("SHARED_MEDIA_SMOKE_REQUIRE_AUDIO", "").strip().casefold() in {
        "1", "true", "yes", "on"
    }
    state = {"finished": False, "video_ready": False, "audio_ready": not require_audio}
    # Keep every wrapper alive until Qt has shut the smoke run down.
    setattr(app, "_shared_media_smoke_refs", (panel, state))

    def finish(code: int):
        if state["finished"]:
            return
        state["finished"] = True
        try:
            panel.stop_preview_workers()
            panel.stop_video_preview()
            panel.close()
        except Exception:
            pass
        app.exit(int(code))

    def frame_ready():
        try:
            if panel.video_widget is not None and panel.video_widget.has_frame():
                state["video_ready"] = True
                if state["audio_ready"]:
                    finish(0)
        except RuntimeError:
            finish(42)

    def poll_audio_ready():
        if state["finished"]:
            return
        monitor = getattr(panel, "audio_monitor", None)
        if monitor is not None and int(getattr(monitor, "buffer_count", 0)) > 0:
            state["audio_ready"] = True
            if state["video_ready"]:
                finish(0)
                return
        QTimer.singleShot(80, poll_audio_ready)

    if panel.video_widget is None:
        QTimer.singleShot(0, lambda: finish(41))
        return True
    panel.video_widget.firstFrameReady.connect(frame_ready)
    if require_audio:
        QTimer.singleShot(80, poll_audio_ready)
    # A fresh compatibility conversion of a real multi-minute AV1 file can
    # take several seconds.  The timeout is long enough to cover that one-time
    # work but still makes broken frozen releases fail deterministically.
    try:
        timeout_ms = int(os.environ.get("SHARED_MEDIA_SMOKE_TIMEOUT_MS", "60000"))
    except ValueError:
        timeout_ms = 60_000
    QTimer.singleShot(max(5_000, min(300_000, timeout_ms)), lambda: finish(44))
    panel.set_path(path, probe_media=True, autoplay=True)
    return True


def register_scan_worker(worker: QThread):
    worker_id = id(worker)
    now = time.monotonic()
    with ACTIVE_SCAN_WORKERS_LOCK:
        ACTIVE_SCAN_WORKERS.add(worker)
        ACTIVE_SCAN_STATE[worker_id] = {
            "kind": type(worker).__name__,
            "registered_at": now,
            "last_progress_at": now,
            "last_progress": 0,
            "last_stall_report": 0.0,
        }
    try:
        worker.progress.connect(
            lambda *args, scan_worker_id=worker_id: note_scan_worker_progress(scan_worker_id, *args)
        )
    except (AttributeError, RuntimeError):
        pass
    # Keep the Python wrapper alive until Qt's native QThread.finished signal.
    # Scanner result signals are deliberately separate because they can be
    # emitted while run() is still unwinding.
    try:
        worker.finished.connect(lambda worker=worker: unregister_scan_worker(worker))
    except RuntimeError:
        pass


def scanner_work_active() -> bool:
    """Cheap process-wide hint used to protect preview/UI responsiveness."""
    with ACTIVE_SCAN_WORKERS_LOCK:
        return bool(ACTIVE_SCAN_WORKERS)


def note_scan_worker_progress(worker_id: int, *args):
    progress = next((value for value in reversed(args) if isinstance(value, int)), None)
    with ACTIVE_SCAN_WORKERS_LOCK:
        state = ACTIVE_SCAN_STATE.get(worker_id)
        if state is None:
            return
        state["last_progress_at"] = time.monotonic()
        if progress is not None:
            state["last_progress"] = int(progress)


def unregister_scan_worker(worker: QThread):
    cancel_scan_processes(worker)
    with ACTIVE_SCAN_WORKERS_LOCK:
        ACTIVE_SCAN_WORKERS.discard(worker)
        ACTIVE_SCAN_STATE.pop(id(worker), None)


def retire_thread_worker(worker: QThread, owners: list):
    """Release a QThread only after Qt reports that its run loop has exited."""
    try:
        owners.remove(worker)
    except ValueError:
        pass
    worker.deleteLater()


def drain_scan_workers():
    """Stop every scanner before Qt tears down its QThread wrappers."""
    with ACTIVE_SCAN_WORKERS_LOCK:
        workers = list(ACTIVE_SCAN_WORKERS)
    for worker in workers:
        try:
            request_cancel = getattr(worker, "request_cancel", None)
            if callable(request_cancel):
                request_cancel()
            worker.requestInterruption()
        except RuntimeError:
            pass

    deadline = time.monotonic() + 3.0
    while time.monotonic() < deadline:
        running = []
        for worker in workers:
            try:
                if worker.isRunning():
                    running.append(worker)
            except RuntimeError:
                continue
        if not running:
            return
        for worker in running:
            try:
                worker.wait(50)
            except RuntimeError:
                pass

    # Some ffmpeg/system probes cannot be interrupted mid-call. A bounded hard
    # stop here is preferable to QThread::~QThread aborting the entire process.
    for worker in workers:
        try:
            if worker.isRunning():
                worker.terminate()
                worker.wait(1500)
        except RuntimeError:
            pass


# `QApplication.aboutToQuit` is the normal cleanup path, but it is not emitted
# when a short-lived window is created without entering Qt's event loop. Drain
# once more before PySide tears down its QThread wrappers in that case.
atexit.register(drain_preview_workers)
atexit.register(drain_scan_workers)


# ---------------------------------------------------------------------------
# File names, media categories, and application settings


class DebugBus(QObject):
    line = Signal(str)


DEBUG_BUS = DebugBus()

FOLDER_PROGRESS_ROLE = Qt.UserRole + 40

IGNORED_FILE_NAMES = {".DS_Store", ".localized", ".delta-downloader.json"}
IGNORED_FOLDER_NAMES = {
    ".fseventsd",
    ".Spotlight-V100",
    ".TemporaryItems",
    ".Trashes",
    # Delta Downloader owns these hidden working/recovery folders. Scanning a
    # growing .part file produces stale results, while quarantined bad downloads
    # have already been conclusively classified and are retained only for recovery.
    ".yt-dlp-temp",
    ".delta-damaged-downloads",
}

LEADING_INDEX_RE = re.compile(r"^\s*\d+\s*(?:[.\-_)]|\s)\s*")
DATE_PREFIX_RE = re.compile(r"^\s*(?:\[\d{4}-\d{2}-\d{2}\]\s*)+")
NATURAL_PART_RE = re.compile(r"(\d+)")
FOLDER_UI_COUNT_RE = re.compile(r"\s*\(\d[\d,]*\s+folders?,\s*\d[\d,]*\s+files?\)\s*$", re.IGNORECASE)


def folder_display_name(name: str) -> str:
    """Remove decoration accidentally persisted by older inline rename code."""
    value = str(name or "").strip()
    decorated = value.startswith(("▼", "▶")) or bool(FOLDER_UI_COUNT_RE.search(value))
    if not decorated:
        return value
    value = FOLDER_UI_COUNT_RE.sub("", value).strip()
    while True:
        cleaned = re.sub(r"^[▼▶]\s*", "", value).strip()
        cleaned = re.sub(r"^Folder:\s*", "", cleaned, flags=re.IGNORECASE).strip()
        if cleaned == value:
            break
        value = cleaned
    return value or str(name or "").strip()

IMAGE_EXTS = {
    ".jpg",
    ".jpeg",
    ".png",
    ".webp",
    ".bmp",
    ".gif",
    ".tif",
    ".tiff",
    ".heic",
    ".heif",
    ".avif",
    ".jxl",
    ".jp2",
    ".ico",
    ".svg",
}
VIDEO_EXTS = {
    ".mp4",
    ".mov",
    ".mkv",
    ".avi",
    ".webm",
    ".m4v",
    ".flv",
    ".wmv",
    ".mpeg",
    ".mpg",
    ".m2v",
    ".ts",
    ".mts",
    ".m2ts",
    ".vob",
    ".ogv",
    ".3gp",
    ".3g2",
    ".asf",
    ".rm",
    ".rmvb",
    ".mxf",
    ".f4v",
    ".m1v",
    ".m2p",
    ".divx",
    ".dv",
    ".y4m",
}
AUDIO_EXTS = {
    ".mp3",
    ".wav",
    ".flac",
    ".m4a",
    ".aac",
    ".ogg",
    ".opus",
    ".aiff",
    ".aif",
    ".alac",
    ".wma",
    ".amr",
    ".ape",
    ".wv",
    ".mka",
    ".mid",
    ".midi",
    ".m4b",
    ".oga",
    ".caf",
    ".ac3",
    ".eac3",
    ".dts",
    ".tta",
    ".spx",
    ".au",
    ".snd",
    ".dsf",
    ".dff",
    ".voc",
    ".ra",
}
DOCUMENT_EXTS = {
    ".pdf",
    ".doc",
    ".docx",
    ".xls",
    ".xlsx",
    ".ppt",
    ".pptx",
    ".txt",
    ".md",
    ".rtf",
    ".csv",
    ".log",
    ".text",
    ".odt",
    ".ods",
    ".odp",
    ".epub",
    ".pages",
    ".numbers",
    ".key",
}
ZIP_ARCHIVE_EXTS = {".zip", ".jar", ".war", ".ear", ".apk", ".ipa", ".cbz", ".xpi", ".whl", ".kmz"}
ARCHIVE_EXTS = ZIP_ARCHIVE_EXTS | {
    ".rar", ".cbr", ".7z", ".cb7", ".tar", ".gz", ".tgz", ".bz2", ".tbz", ".tbz2",
    ".xz", ".txz", ".dmg", ".pkg", ".iso",
}
CODE_EXTS = {
    ".py",
    ".js",
    ".ts",
    ".tsx",
    ".jsx",
    ".html",
    ".css",
    ".json",
    ".xml",
    ".yaml",
    ".yml",
    ".toml",
    ".swift",
    ".java",
    ".c",
    ".cpp",
    ".h",
    ".hpp",
    ".sh",
    ".sql",
}
DATA_EXTS = {".sqlite", ".db", ".parquet", ".feather", ".jsonl", ".ndjson", ".pkl"}
EMPTY_FILE_IS_INVALID_EXTS = (
    IMAGE_EXTS
    | VIDEO_EXTS
    | AUDIO_EXTS
    | ARCHIVE_EXTS
    | {
        ".pdf",
        ".doc",
        ".docx",
        ".xls",
        ".xlsx",
        ".ppt",
        ".pptx",
        ".rtf",
        ".odt",
        ".ods",
        ".odp",
        ".epub",
        ".pages",
        ".numbers",
        ".key",
        ".sqlite",
        ".db",
        ".parquet",
        ".feather",
        ".pkl",
    }
)

TYPE_FOLDER_NAMES = {
    "Image": "Images",
    "Video": "Videos",
    "Audio": "Audio",
    "Document": "Documents",
    "Archive": "Archives",
    "Code": "Code",
    "Data": "Data",
    "No Extension": "No Extension",
    "Other": "Other",
}


def app_settings() -> QSettings:
    return QSettings(SETTINGS_ORG, SETTINGS_APP)


def settings_bool(settings: QSettings, key: str, default: bool) -> bool:
    value = settings.value(key, default)
    if isinstance(value, bool):
        return value
    return str(value).strip().lower() in {"1", "true", "yes", "on"}


DEBUG_PRIVATE_STATE_TOKENS = (
    "path",
    "file",
    "folder",
    "filename",
    "dirname",
    "source",
    "target",
    "url",
)

# These fields describe the playback machinery, never a user-selected name or
# location.  Keep them visible even though words such as ``source`` would have
# triggered the older broad privacy rule.
DEBUG_SAFE_MEDIA_STATE_KEYS = {
    "app",
    "audio_codec",
    "backend_message",
    "buffer_percent",
    "cache_state",
    "container",
    "decision",
    "duration_ms",
    "elapsed_ms",
    "encoder",
    "error",
    "error_code",
    "extension",
    "frame_height",
    "frame_width",
    "has_audio",
    "has_video",
    "item_id",
    "kind",
    "logical_paused",
    "media_status",
    "mime",
    "occurrences",
    "output_bytes",
    "pixel_format",
    "playback_state",
    "position_ms",
    "proxy_request_id",
    "qt_category",
    "qt_severity",
    "request_id",
    "resolution",
    "source_bytes",
    "source_exists",
    "source_kind",
    "surface",
    "video_codec",
}


# ---------------------------------------------------------------------------
# Bounded diagnostics and privacy filtering


def _debug_text_contains_private_location(text: str) -> bool:
    """Recognize absolute locations without mistaking labels such as A/B."""
    return bool(
        re.search(r"\bfile\s*:", text, re.IGNORECASE)
        or re.search(r"(?:^|[\s'\"=(:])/(?!/)[^\s'\"<>]+", text)
        or re.search(r"(?:^|[\s'\"=(:])[A-Za-z]:[\\/][^\s'\"<>]*", text)
        or re.search(r"(?:^|[\s'\"=(:])\\\\[^\\\s]+\\[^\s'\"<>]*", text)
    )


def privacy_safe_debug_value(key: str, value) -> str:
    """Keep diagnostics useful without exposing names from the user's library."""
    normalized_key = str(key).casefold().replace("-", "_")
    if (
        normalized_key not in DEBUG_SAFE_MEDIA_STATE_KEYS
        and any(token in normalized_key for token in DEBUG_PRIVATE_STATE_TOKENS)
    ):
        return "<redacted>"
    if normalized_key in {"detail", "description"}:
        # Backend details routinely contain the complete media URL. The error
        # enum beside this field is stable and useful; the backend prose is not
        # worth leaking a local filename for.
        return "<backend detail omitted>"
    try:
        text = str(value)
    except Exception:
        return "<unprintable>"
    text = re.sub(r"https?://[^\s'\"<>]+", "<url>", text, flags=re.IGNORECASE)
    if _debug_text_contains_private_location(text):
        return "<redacted-path>"
    return text


def persistent_diagnostic_path() -> Path:
    return Path.home() / "Library" / "Logs" / DIAGNOSTIC_FOLDER / "watchdog.log"


def _write_persistent_diagnostic_batch(lines: Sequence[str]):
    """Write one queued batch away from Qt's GUI and multimedia threads."""
    if not lines:
        return
    with PERSISTENT_DIAGNOSTIC_LOCK:
        try:
            path = persistent_diagnostic_path()
            path.parent.mkdir(parents=True, exist_ok=True)
            if path.exists() and path.stat().st_size > 512 * 1024:
                previous = path.with_suffix(".previous.log")
                try:
                    previous.unlink(missing_ok=True)
                    path.replace(previous)
                except OSError:
                    # A failed rename must not turn a normally bounded diagnostic
                    # into a file that grows forever. Preserve the new evidence
                    # and recover the cap by truncating the active generation.
                    try:
                        path.write_text(
                            "[diagnostic rotation failed; active log restarted]\n",
                            encoding="utf-8",
                        )
                    except OSError:
                        return
            with path.open("a", encoding="utf-8") as handle:
                handle.write("\n".join(str(line) for line in lines) + "\n")
        except OSError:
            pass


def _persistent_diagnostic_writer():
    """Write queued diagnostics promptly, always away from the GUI thread."""
    while True:
        first = PERSISTENT_DIAGNOSTIC_QUEUE.get()
        batch = [first]
        try:
            while len(batch) < 256:
                try:
                    batch.append(PERSISTENT_DIAGNOSTIC_QUEUE.get_nowait())
                except queue.Empty:
                    break
            queued_line_count = len(batch)
            dropped = take_persistent_diagnostic_drop_count()
            if dropped:
                batch.insert(
                    0,
                    (
                        f"[{datetime.now().strftime('%H:%M:%S.%f')[:-3]}] "
                        "diagnostic-overflow: older low-level records were coalesced"
                        f" | dropped={dropped} queue_limit={PERSISTENT_DIAGNOSTIC_QUEUE_LIMIT}"
                    ),
                )
            _write_persistent_diagnostic_batch(batch)
        finally:
            # The optional overflow summary is synthesized by this writer and
            # was never put on the queue. Only acknowledge actual queued lines;
            # otherwise Queue.task_done() raises and permanently kills the
            # diagnostic thread precisely when it first comes under pressure.
            for _line in range(queued_line_count):
                PERSISTENT_DIAGNOSTIC_QUEUE.task_done()


def ensure_persistent_diagnostic_writer():
    global PERSISTENT_DIAGNOSTIC_THREAD
    with PERSISTENT_DIAGNOSTIC_START_LOCK:
        thread = PERSISTENT_DIAGNOSTIC_THREAD
        if thread is not None and thread.is_alive():
            return
        thread = threading.Thread(
            target=_persistent_diagnostic_writer,
            name="preview-diagnostic-writer",
            daemon=True,
        )
        PERSISTENT_DIAGNOSTIC_THREAD = thread
        thread.start()


def take_persistent_diagnostic_drop_count() -> int:
    global PERSISTENT_DIAGNOSTIC_DROPPED
    with PERSISTENT_DIAGNOSTIC_DROP_LOCK:
        dropped = PERSISTENT_DIAGNOSTIC_DROPPED
        PERSISTENT_DIAGNOSTIC_DROPPED = 0
    return dropped


def _record_persistent_diagnostic_drop(count: int = 1) -> None:
    global PERSISTENT_DIAGNOSTIC_DROPPED
    with PERSISTENT_DIAGNOSTIC_DROP_LOCK:
        PERSISTENT_DIAGNOSTIC_DROPPED += max(0, int(count))


def append_persistent_diagnostic(line: str):
    """Queue restart-safe diagnostics without blocking media presentation.

    The newest evidence is the most useful after a fault. If disk writing falls
    behind a decoder burst, discard one old queued transition instead of letting
    an unbounded queue consume memory for the rest of the app session.
    """
    try:
        ensure_persistent_diagnostic_writer()
        value = str(line)
        try:
            PERSISTENT_DIAGNOSTIC_QUEUE.put_nowait(value)
        except queue.Full:
            try:
                PERSISTENT_DIAGNOSTIC_QUEUE.get_nowait()
                PERSISTENT_DIAGNOSTIC_QUEUE.task_done()
                _record_persistent_diagnostic_drop()
            except queue.Empty:
                pass
            try:
                PERSISTENT_DIAGNOSTIC_QUEUE.put_nowait(value)
            except queue.Full:
                _record_persistent_diagnostic_drop()
    except Exception:
        pass


def flush_persistent_diagnostics(timeout: float = 2.0):
    """Wait briefly for queued lines before saving or interpreter shutdown."""
    deadline = time.monotonic() + max(0.0, float(timeout))
    while time.monotonic() < deadline:
        if PERSISTENT_DIAGNOSTIC_QUEUE.unfinished_tasks <= 0:
            return
        time.sleep(0.01)


def load_previous_watchdog_diagnostics():
    try:
        path = persistent_diagnostic_path()
        previous = path.with_suffix(".previous.log")
        if not path.exists() and not previous.exists():
            return
        lines: List[str] = []
        for candidate in (previous, path):
            if candidate.exists():
                lines.extend(candidate.read_text(encoding="utf-8", errors="replace").splitlines())
        lines = lines[-1500:]
    except OSError:
        return
    if not lines:
        return
    with DEBUG_LOCK:
        DEBUG_LINES.append("--- Recent saved diagnostics (including media preview) ---")
        DEBUG_LINES.extend(lines)
        if len(DEBUG_LINES) > DEBUG_LINE_LIMIT:
            del DEBUG_LINES[: len(DEBUG_LINES) - DEBUG_LINE_LIMIT]


atexit.register(flush_persistent_diagnostics)


def combined_diagnostics_text() -> str:
    """Return rotated persistence plus current memory, without duplicate lines."""
    flush_persistent_diagnostics()
    disk_lines: List[str] = []
    path = persistent_diagnostic_path()
    for candidate in (path.with_suffix(".previous.log"), path):
        try:
            if candidate.exists():
                disk_lines.extend(
                    candidate.read_text(encoding="utf-8", errors="replace").splitlines()
                )
        except OSError:
            continue
    with DEBUG_LOCK:
        memory_lines = list(DEBUG_LINES)
    result: List[str] = []
    seen = set()
    for line in [*disk_lines, *memory_lines]:
        if line in seen:
            continue
        seen.add(line)
        result.append(line)
    return "\n".join(result)


def _routine_preview_transition_is_terminal(
    message: str,
    safe_state: Dict[str, str],
) -> bool:
    """Retain the useful end of a noisy Qt transition burst immediately."""
    if message == "Qt media capabilities changed":
        return any(
            str(safe_state.get(key, "")).casefold() == "true"
            for key in ("has_video", "has_audio")
        ) or str(safe_state.get("player_error", "NoError")) != "NoError"
    if message == "Qt media status changed":
        status = str(
            safe_state.get("media_status", safe_state.get("status", ""))
        )
        return status in {"BufferedMedia", "InvalidMedia", "EndOfMedia"}
    if message == "Qt playback state changed":
        state = str(
            safe_state.get("playback_state", safe_state.get("state", ""))
        )
        return state in {"PlayingState", "PausedState"}
    return False


def debug_log(source: str, message: str, *, force: bool = False, **state):
    safe_state = {str(key): privacy_safe_debug_value(str(key), value) for key, value in state.items()}
    signature = tuple(sorted((key, repr(value)) for key, value in safe_state.items()))
    preview_source = str(source).startswith(PREVIEW_DEBUG_SOURCE_PREFIXES)
    if preview_source:
        context = tuple(
            (key, safe_state.get(key, ""))
            for key in ("surface", "item_id", "request_id", "qt_category")
        )
        state_key = (source, message, context)
    else:
        state_key = (source, message)
    now = time.monotonic()
    message_text = str(message)
    message_folded = message_text.casefold()
    important = any(
        token in message_folded
        for token in ("error", "failed", "cannot", "retry", "ignored", "stalled", "unresponsive")
    )
    routine_interval = ROUTINE_PREVIEW_LOG_INTERVALS.get(message_text, 0.0)
    if routine_interval and safe_state.get("surface"):
        rate_key = (
            source,
            message_text,
            safe_state.get("surface", ""),
            safe_state.get("item_id", ""),
            safe_state.get("request_id", ""),
        )
        terminal = _routine_preview_transition_is_terminal(message_text, safe_state)
        with DEBUG_LOCK:
            previous_emit = DEBUG_RATE_LAST.get(rate_key, 0.0)
            if not important and not terminal and now - previous_emit < routine_interval:
                return
            DEBUG_RATE_LAST.pop(rate_key, None)
            DEBUG_RATE_LAST[rate_key] = now
            while len(DEBUG_RATE_LAST) > DEBUG_STATE_LIMIT:
                try:
                    DEBUG_RATE_LAST.pop(next(iter(DEBUG_RATE_LAST)))
                except StopIteration:
                    break
    bits = []
    for key, value in safe_state.items():
        bits.append(f"{key}={value}")
    line = f"[{datetime.now().strftime('%H:%M:%S.%f')[:-3]}] {source}: {message}"
    if bits:
        line += " | " + " ".join(bits)
    with DEBUG_LOCK:
        previous = DEBUG_LAST_STATE.get(state_key)
        # The debug window is for transitions and failures, not per-frame/event spam.
        if not force and previous is not None and previous[0] == signature:
            return
        if (
            not force
            and preview_source
            and "progress" in message.casefold()
            and previous is not None
            and now - previous[1] < 1.0
        ):
            return
        if (
            not force
            and not preview_source
            and previous is not None
            and not important
            and now - previous[1] < 0.35
        ):
            return
        # Request ids intentionally create fresh keys. Bound the deduplication
        # index so a long media-browsing session cannot retain every old item.
        DEBUG_LAST_STATE.pop(state_key, None)
        DEBUG_LAST_STATE[state_key] = (signature, now)
        while len(DEBUG_LAST_STATE) > DEBUG_STATE_LIMIT:
            try:
                DEBUG_LAST_STATE.pop(next(iter(DEBUG_LAST_STATE)))
            except StopIteration:
                break
        DEBUG_LINES.append(line)
        if len(DEBUG_LINES) > DEBUG_LINE_LIMIT:
            del DEBUG_LINES[: len(DEBUG_LINES) - DEBUG_LINE_LIMIT]
    source_text = str(source)
    if (
        source_text == "watchdog"
        or "window-trace" in source_text
        or source_text == "window"
        or source_text.startswith("interaction-")
        or source_text.startswith(PREVIEW_DEBUG_SOURCE_PREFIXES)
    ):
        append_persistent_diagnostic(line)
    try:
        DEBUG_BUS.line.emit(line)
    except RuntimeError:
        pass


def install_diagnostic_exception_hook():
    """Mirror uncaught Python/Qt-slot exceptions into the persistent debug log."""
    previous_hook = sys.excepthook

    def diagnostic_excepthook(exc_type, exc_value, exc_tb):
        try:
            formatted = "".join(traceback.format_exception(exc_type, exc_value, exc_tb)).rstrip()
            line = f"[{datetime.now().strftime('%H:%M:%S.%f')[:-3]}] python-exception: uncaught exception\n{formatted}"
            with DEBUG_LOCK:
                DEBUG_LINES.append(line)
                if len(DEBUG_LINES) > DEBUG_LINE_LIMIT:
                    del DEBUG_LINES[: len(DEBUG_LINES) - DEBUG_LINE_LIMIT]
            append_persistent_diagnostic(line)
            try:
                DEBUG_BUS.line.emit(line)
            except RuntimeError:
                pass
        except Exception:
            pass
        try:
            previous_hook(exc_type, exc_value, exc_tb)
        except Exception:
            pass

    sys.excepthook = diagnostic_excepthook


install_diagnostic_exception_hook()


def preview_item_id(path: Optional[Path]) -> str:
    """Return a stable anonymous correlation key for one selected item."""
    if path is None:
        return "none"
    try:
        raw = os.fsencode(os.path.normpath(os.fspath(Path(path))))
    except Exception:
        raw = repr(path).encode("utf-8", errors="replace")
    return hashlib.sha1(raw).hexdigest()[:10]


def qt_enum_name(value) -> str:
    """Render PySide enums consistently across Qt versions."""
    name = getattr(value, "name", None)
    if name:
        return str(name)
    text = str(value)
    return text.rsplit(".", 1)[-1] if "." in text else text


def preview_trace(
    surface: str,
    message: str,
    path: Optional[Path] = None,
    *,
    force: bool = False,
    **state,
):
    """Write one privacy-safe, correlated preview transition to Debug."""
    payload = {
        "surface": str(surface),
        "item_id": preview_item_id(path),
        "extension": (Path(path).suffix.lower() or "none") if path is not None else "none",
    }
    # Associate asynchronous source/frame/audio transitions with the user
    # action that triggered them.  The bounded window avoids falsely linking
    # unrelated background activity minutes later.
    try:
        interaction_state = globals().get("INTERACTION_DIAGNOSTIC_STATE", {})
        started_at = float(interaction_state.get("started_at", 0.0) or 0.0)
        if started_at and time.monotonic() - started_at <= 3.0:
            payload["interaction_id"] = int(interaction_state.get("interaction_id", 0) or 0)
            payload["interaction_kind"] = str(interaction_state.get("kind", "unknown"))
    except (TypeError, ValueError):
        pass
    payload.update(state)
    debug_log("media-preview", message, force=force, **payload)


def sanitized_thread_snapshot() -> str:
    """Return stack locations only: no source lines, local values, or media names."""
    try:
        frames = sys._current_frames()
    except Exception:
        return "unavailable"
    names = {thread.ident: thread.name for thread in threading.enumerate()}
    ordered_ids = sorted(
        frames,
        key=lambda ident: (
            0 if names.get(ident) == "MainThread" else 1,
            0 if "folder-manager" in names.get(ident, "").casefold() else 1,
            names.get(ident, ""),
        ),
    )
    snapshots = []
    for ident in ordered_ids[:16]:
        frame = frames.get(ident)
        if frame is None:
            continue
        stack = traceback.extract_stack(frame, limit=10)
        locations = [
            f"{Path(entry.filename).name}:{entry.lineno}:{entry.name}"
            for entry in stack[-6:]
        ]
        snapshots.append(f"{names.get(ident, 'thread')}=>" + ">".join(locations))
    return " || ".join(snapshots) if snapshots else "empty"


def watchdog_runtime_state() -> Dict[str, object]:
    with ACTIVE_SCAN_WORKERS_LOCK:
        scan_kinds = Counter(str(state.get("kind", "scan")) for state in ACTIVE_SCAN_STATE.values())
        scan_summary = ",".join(f"{kind}:{count}" for kind, count in sorted(scan_kinds.items())) or "none"
    with VIDEO_FINGERPRINT_CACHE_LOCK:
        fingerprint_cache = len(VIDEO_FINGERPRINT_CACHE)
        fingerprint_waiting = len(VIDEO_FINGERPRINT_INFLIGHT)
    with FINGERPRINT_DIAGNOSTICS_LOCK:
        fingerprint_stats = ",".join(
            f"{key}:{value}" for key, value in sorted(FINGERPRINT_DIAGNOSTICS.items())
        ) or "none"
    with INTERACTION_DIAGNOSTIC_LOCK:
        interaction = dict(INTERACTION_DIAGNOSTIC_STATE)
    interaction_age_ms = (
        round(max(0.0, time.monotonic() - float(interaction.get("started_at", 0.0))) * 1000)
        if interaction.get("started_at")
        else 0
    )
    return {
        "scanners": scan_summary,
        "fingerprint_cache": fingerprint_cache,
        "fingerprint_inflight": fingerprint_waiting,
        "fingerprint_stats": fingerprint_stats,
        "last_interaction_id": interaction.get("interaction_id", 0),
        "last_interaction_kind": interaction.get("kind", "none"),
        "last_interaction_pending": bool(interaction.get("pending", False)),
        "last_interaction_age_ms": interaction_age_ms,
        "last_interaction_widget": interaction.get("widget_class", "none"),
    }


class ApplicationWatchdogHeartbeat(QObject):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.timer = QTimer(self)
        self.timer.setInterval(200)
        try:
            self.timer.setTimerType(Qt.TimerType.PreciseTimer)
        except Exception:
            pass
        self.timer.timeout.connect(self.beat)

    def start(self):
        self.beat()
        self.timer.start()

    def beat(self):
        global GUI_HEARTBEAT_AT, GUI_HEARTBEAT_ACTIVE
        with GUI_HEARTBEAT_LOCK:
            GUI_HEARTBEAT_AT = time.monotonic()
            GUI_HEARTBEAT_ACTIVE = application_is_active()


def application_watchdog_loop():
    unresponsive_since: Optional[float] = None
    last_gui_report = 0.0
    while not APP_WATCHDOG_STOP.wait(0.5):
        now = time.monotonic()
        with GUI_HEARTBEAT_LOCK:
            heartbeat_age = max(0.0, now - GUI_HEARTBEAT_AT)
            app_active = GUI_HEARTBEAT_ACTIVE
        with ACTIVE_SCAN_WORKERS_LOCK:
            scan_states = [(worker_id, dict(state)) for worker_id, state in ACTIVE_SCAN_STATE.items()]

        if heartbeat_age >= 3.0 and (app_active or scan_states):
            if unresponsive_since is None:
                unresponsive_since = now - heartbeat_age
            if now - last_gui_report >= 30.0:
                last_gui_report = now
                debug_log(
                    "watchdog",
                    "GUI event loop unresponsive",
                    force=True,
                    seconds=f"{heartbeat_age:.1f}",
                    stacks=sanitized_thread_snapshot(),
                    **watchdog_runtime_state(),
                )
        elif unresponsive_since is not None:
            debug_log(
                "watchdog",
                "GUI event loop recovered",
                force=True,
                seconds=f"{now - unresponsive_since:.1f}",
                **watchdog_runtime_state(),
            )
            unresponsive_since = None
            last_gui_report = 0.0

        for worker_id, state in scan_states:
            idle = now - float(state.get("last_progress_at", now))
            last_report = float(state.get("last_stall_report", 0.0))
            if idle < 25.0 or now - last_report < 60.0:
                continue
            with ACTIVE_SCAN_WORKERS_LOCK:
                current = ACTIVE_SCAN_STATE.get(worker_id)
                if current is None:
                    continue
                current["last_stall_report"] = now
            debug_log(
                "watchdog",
                "scanner made no progress",
                force=True,
                scanner=state.get("kind", "scan"),
                seconds=f"{idle:.1f}",
                progress=state.get("last_progress", 0),
                stacks=sanitized_thread_snapshot(),
                **watchdog_runtime_state(),
            )


def start_application_watchdog(app: QApplication):
    global APP_WATCHDOG_HEARTBEAT, APP_WATCHDOG_THREAD
    install_window_diagnostic_filter(app)
    APP_WATCHDOG_STOP.clear()
    APP_WATCHDOG_HEARTBEAT = ApplicationWatchdogHeartbeat(app)
    APP_WATCHDOG_HEARTBEAT.start()
    APP_WATCHDOG_THREAD = threading.Thread(
        target=application_watchdog_loop,
        name="folder-manager-watchdog",
        daemon=True,
    )
    APP_WATCHDOG_THREAD.start()


def stop_application_watchdog():
    APP_WATCHDOG_STOP.set()
    thread = APP_WATCHDOG_THREAD
    if thread is not None and thread.is_alive() and thread is not threading.current_thread():
        thread.join(timeout=1.0)
    flush_persistent_diagnostics()


WINDOW_DIAGNOSTIC_LAST_INPUT = {
    "time": 0.0,
    "kind": "none",
    "key": "",
    "modifiers": "",
    "window": "",
}
WINDOW_DIAGNOSTIC_FILTER = None
INTERACTION_DIAGNOSTIC_LOCK = threading.Lock()
INTERACTION_DIAGNOSTIC_STATE = {
    "interaction_id": 0,
    "kind": "none",
    "started_at": 0.0,
    "pending": False,
    "widget_class": "none",
}


def _diagnostic_widget_name(widget) -> str:
    if widget is None:
        return "none"
    try:
        title = widget.windowTitle() if hasattr(widget, "windowTitle") else ""
    except RuntimeError:
        title = "<deleted>"
    try:
        cls = type(widget).__name__
    except Exception:
        cls = "unknown"
    return f"{cls}:{title}" if title else cls


def _diagnostic_key_name(event) -> str:
    try:
        key = event.key()
    except Exception:
        return "unknown"
    names = {
        int(Qt.Key_Escape): "Escape",
        int(Qt.Key_Space): "Space",
        int(Qt.Key_Return): "Return",
        int(Qt.Key_Enter): "Enter",
        int(Qt.Key_W): "W",
        int(Qt.Key_Q): "Q",
    }
    try:
        numeric = getattr(key, "value", key)
        return names.get(int(numeric), str(numeric))
    except Exception:
        return str(key)


def _interaction_key_name(event) -> Optional[str]:
    """Return only navigation/control keys; never reconstruct typed text."""
    try:
        numeric = int(getattr(event.key(), "value", event.key()))
    except Exception:
        return None
    names = {
        int(Qt.Key_Escape): "Escape",
        int(Qt.Key_Space): "Space",
        int(Qt.Key_Return): "Return",
        int(Qt.Key_Enter): "Enter",
        int(Qt.Key_Left): "Left",
        int(Qt.Key_Right): "Right",
        int(Qt.Key_Up): "Up",
        int(Qt.Key_Down): "Down",
        int(Qt.Key_PageUp): "PageUp",
        int(Qt.Key_PageDown): "PageDown",
        int(Qt.Key_Home): "Home",
        int(Qt.Key_End): "End",
        int(Qt.Key_Delete): "Delete",
        int(Qt.Key_Backspace): "Backspace",
        int(Qt.Key_Tab): "Tab",
        int(Qt.Key_Backtab): "Backtab",
        int(Qt.Key_F): "F",
    }
    key_name = names.get(numeric)
    if key_name is not None:
        return key_name
    try:
        modifiers = event.modifiers()
        command = bool(modifiers & (Qt.ControlModifier | Qt.MetaModifier))
    except Exception:
        command = False
    if command and numeric == int(Qt.Key_W):
        return "Command+W"
    if command and numeric == int(Qt.Key_Q):
        return "Command+Q"
    return None


def _interaction_short_label(value, limit: int = 72) -> str:
    """Sanitize static control identifiers without reading editable content."""
    try:
        text = " ".join(str(value or "").split())
    except Exception:
        return "unavailable"
    if not text:
        return "none"
    if re.search(r"https?://", text, re.IGNORECASE) or _debug_text_contains_private_location(text):
        return "<redacted>"
    return text if len(text) <= limit else text[: max(1, limit - 1)] + "…"


def _interaction_semantic_widget(obj):
    """Resolve viewport/editor children to the control the user perceives."""
    widget = obj if isinstance(obj, QWidget) else None
    fallback = widget
    for _depth in range(8):
        if widget is None:
            break
        if isinstance(
            widget,
            (QAbstractButton, QAbstractSlider, QAbstractItemView, QComboBox, QTabBar),
        ):
            return widget
        try:
            widget = widget.parentWidget()
        except RuntimeError:
            break
    return fallback


def _interaction_editor_ancestor(obj) -> bool:
    widget = obj if isinstance(obj, QWidget) else None
    for _depth in range(8):
        if widget is None:
            return False
        if isinstance(widget, (QLineEdit, QTextEdit, QPlainTextEdit)):
            return True
        try:
            widget = widget.parentWidget()
        except RuntimeError:
            return False
    return False


def _interaction_widget_snapshot(widget) -> Dict[str, object]:
    """Collect bounded numeric/control state without file names or cell text."""
    if widget is None:
        return {"alive": False}
    try:
        state: Dict[str, object] = {
            "alive": True,
            "widget_class": type(widget).__name__,
            "object_name": _interaction_short_label(widget.objectName()),
            "enabled": bool(widget.isEnabled()),
            "visible": bool(widget.isVisible()),
            "focus": bool(widget.hasFocus()),
        }
        if isinstance(widget, QAbstractButton):
            state.update(
                control_label=_interaction_short_label(widget.text()),
                checkable=bool(widget.isCheckable()),
                checked=bool(widget.isChecked()) if widget.isCheckable() else False,
                down=bool(widget.isDown()),
            )
        elif isinstance(widget, QAbstractSlider):
            state.update(
                value=int(widget.value()),
                minimum=int(widget.minimum()),
                maximum=int(widget.maximum()),
                slider_position=int(widget.sliderPosition()),
                slider_down=bool(widget.isSliderDown()),
            )
        elif isinstance(widget, QAbstractItemView):
            model = widget.model()
            current = widget.currentIndex()
            selection_ranges = 0
            try:
                selection = widget.selectionModel().selection() if widget.selectionModel() else None
                selection_ranges = int(selection.count()) if selection is not None else 0
            except (AttributeError, RuntimeError, TypeError, ValueError):
                selection_ranges = -1
            state.update(
                row_count=int(model.rowCount()) if model is not None else 0,
                column_count=int(model.columnCount()) if model is not None else 0,
                current_row=int(current.row()) if current.isValid() else -1,
                current_column=int(current.column()) if current.isValid() else -1,
                selection_ranges=selection_ranges,
                vertical_scroll=int(widget.verticalScrollBar().value()),
                horizontal_scroll=int(widget.horizontalScrollBar().value()),
            )
        elif isinstance(widget, QComboBox):
            state.update(current_index=int(widget.currentIndex()), control_count=int(widget.count()))
        elif isinstance(widget, QTabBar):
            state.update(current_index=int(widget.currentIndex()), control_count=int(widget.count()))
        return state
    except RuntimeError:
        return {"alive": False, "widget_class": type(widget).__name__}
    except Exception as exc:
        return {
            "alive": True,
            "widget_class": type(widget).__name__,
            "snapshot_error": type(exc).__name__,
        }


def _active_preview_interaction_state() -> str:
    """Summarize shared player intent/transport without exposing media names."""
    summaries: List[str] = []
    for owner in list(VIDEO_PLAYBACK_OWNERS):
        try:
            current = getattr(owner, "current_path", None)
            if current is None:
                continue
            if hasattr(owner, "logical_playback_paused"):
                logical_paused = bool(owner.logical_playback_paused())
            else:
                logical_paused = bool(getattr(owner, "playback_paused_by_user", False))
            player = getattr(owner, "media_player", None)
            snapshot = qmedia_player_snapshot(player)
            video_widget = getattr(owner, "video_widget", None)
            frame = video_frame_snapshot(video_widget)
            audio = audio_buffer_snapshot(getattr(owner, "audio_monitor", None))
            surface = preview_surface_snapshot(owner)
            summaries.append(
                ":".join(
                    (
                        str(surface.get("surface_role", type(owner).__name__)),
                        preview_item_id(current),
                        preview_source_kind(owner).replace(" ", "_"),
                        "paused" if logical_paused else "playing",
                        str(snapshot.get("player_playback_state", "unknown")),
                        f"pos{snapshot.get('position_ms', 0)}",
                        f"frames{frame.get('frames_converted', 0)}",
                        f"audio{audio.get('audio_buffers_decoded', 0)}",
                        "muted" if snapshot.get("audio_output_muted") else "sound",
                        "controls" if surface.get("play_button_visible") else "no-controls",
                        "owner-ok" if surface.get("ownership_ok") else "OWNER-VIOLATION",
                    )
                )
            )
            if len(summaries) >= 6:
                break
        except (AttributeError, RuntimeError, TypeError, ValueError):
            continue
    return ";".join(summaries[:6]) or "none"


class DiagnosticWindowEventFilter(QObject):
    """Correlate privacy-safe user input with the UI/player state it produced."""

    def __init__(self, parent=None):
        super().__init__(parent)
        self.interaction_sequence = 0
        self.last_dense_event: Dict[Tuple[object, ...], float] = {}
        # QApplication's event filter can see the same physical mouse/wheel
        # event once for the viewport and again while Qt propagates it through
        # parent widgets. Retain a very small identity/fingerprint window so a
        # single gesture produces one useful trace instead of a burst of near-
        # identical snapshots and timers.
        self.recent_physical_event_objects: deque = deque(maxlen=64)
        self.recent_physical_event_fingerprints: Dict[Tuple[object, ...], float] = {}
        self.stabilization_generations: Dict[Tuple[int, str], int] = {}

    @staticmethod
    def _event_modifiers(event) -> str:
        try:
            modifiers = event.modifiers()
            return str(getattr(modifiers, "value", modifiers))
        except Exception:
            return "unknown"

    @staticmethod
    def _mouse_payload(widget, event) -> Dict[str, object]:
        payload: Dict[str, object] = {}
        try:
            payload["mouse_button"] = qt_enum_name(event.button())
        except Exception:
            payload["mouse_button"] = "unknown"
        try:
            position = event.position()
            payload["local_x"] = round(float(position.x()), 1)
            payload["local_y"] = round(float(position.y()), 1)
        except Exception:
            pass
        try:
            payload["widget_width"] = int(widget.width())
            payload["widget_height"] = int(widget.height())
        except (AttributeError, RuntimeError, TypeError, ValueError):
            pass
        return payload

    def _dense_event_allowed(self, signature: Tuple[object, ...], interval: float = 0.2) -> bool:
        now = time.monotonic()
        previous = self.last_dense_event.get(signature, 0.0)
        if now - previous < interval:
            return False
        self.last_dense_event[signature] = now
        if len(self.last_dense_event) > 256:
            cutoff = now - 10.0
            self.last_dense_event = {
                key: value for key, value in self.last_dense_event.items() if value >= cutoff
            }
        return True

    @staticmethod
    def _dense_widget_key(widget) -> Tuple[str, str, str]:
        """Identify a semantic control without retaining short-lived wrappers.

        Qt can expose a different Python wrapper while one native wheel gesture
        propagates through a scroll area's viewport and owner. Using ``id`` made
        each wrapper look unique and defeated the intended interaction throttle.
        """
        if widget is None:
            return ("none", "none", "none")
        try:
            widget_class = type(widget).__name__
        except Exception:
            widget_class = "unknown"
        try:
            object_name = str(widget.objectName() or "none")
        except (AttributeError, RuntimeError):
            object_name = "none"
        try:
            window = widget.window()
            window_class = type(window).__name__ if window is not None else "none"
        except (AttributeError, RuntimeError):
            window_class = "none"
        return (widget_class, object_name, window_class)

    @staticmethod
    def _event_numeric(value) -> object:
        try:
            return int(getattr(value, "value", value))
        except (TypeError, ValueError):
            return str(value)

    def _physical_event_fingerprint(self, event) -> Tuple[object, ...]:
        """Build a propagation-stable signature without retaining private data."""
        parts: List[object] = ["event", self._event_numeric(event.type())]
        for accessor in ("timestamp", "button", "buttons", "key"):
            try:
                value = getattr(event, accessor)()
            except (AttributeError, RuntimeError, TypeError):
                continue
            parts.extend((accessor, self._event_numeric(value)))
        try:
            position = event.globalPosition()
            parts.extend(
                (
                    "global-position",
                    round(float(position.x()), 1),
                    round(float(position.y()), 1),
                )
            )
        except (AttributeError, RuntimeError, TypeError, ValueError):
            pass
        try:
            delta = event.angleDelta()
            parts.extend(("wheel-delta", int(delta.x()), int(delta.y())))
        except (AttributeError, RuntimeError, TypeError, ValueError):
            pass
        try:
            parts.extend(("auto-repeat", bool(event.isAutoRepeat())))
        except (AttributeError, RuntimeError, TypeError):
            pass
        return tuple(parts)

    def _claim_physical_event(self, event) -> bool:
        """Return True only for the first actionable receiver of an event."""
        now = time.monotonic()
        while self.recent_physical_event_objects:
            _previous_event, seen_at = self.recent_physical_event_objects[0]
            if now - seen_at <= 0.25:
                break
            self.recent_physical_event_objects.popleft()
        if any(event is previous for previous, _seen_at in self.recent_physical_event_objects):
            return False

        fingerprint = self._physical_event_fingerprint(event)
        previous = self.recent_physical_event_fingerprints.get(fingerprint, 0.0)
        # Propagation completes synchronously. A short fallback interval also
        # catches platforms that expose a fresh Python wrapper for the same Qt
        # event, without swallowing a later genuine click or wheel gesture.
        if now - previous < 0.05:
            return False

        self.recent_physical_event_objects.append((event, now))
        self.recent_physical_event_fingerprints[fingerprint] = now
        if len(self.recent_physical_event_fingerprints) > 256:
            cutoff = now - 0.5
            self.recent_physical_event_fingerprints = {
                key: value
                for key, value in self.recent_physical_event_fingerprints.items()
                if value >= cutoff
            }
        return True

    def _record_interaction(
        self,
        widget,
        kind: str,
        *,
        event_payload: Optional[Dict[str, object]] = None,
        source_event=None,
    ) -> bool:
        if not VERBOSE_INTERACTION_DIAGNOSTICS:
            return False
        if source_event is not None:
            # Non-widget delivery targets are an implementation detail (and
            # produced the old `alive=False` duplicates). Let propagation reach
            # the first real control before claiming the event.
            if widget is None or not self._claim_physical_event(source_event):
                return False
        self.interaction_sequence += 1
        interaction_id = self.interaction_sequence
        started_at = time.monotonic()
        before = _interaction_widget_snapshot(widget)
        event_fields = dict(event_payload or {})
        before_preview_state = _active_preview_interaction_state()
        payload = {
            "interaction_id": interaction_id,
            "kind": kind,
            "modifiers": str(event_fields.pop("modifiers", "unknown")),
            **before,
            **event_fields,
            "preview_state": before_preview_state,
        }
        debug_log("interaction-input", "user action received", force=True, **payload)
        with INTERACTION_DIAGNOSTIC_LOCK:
            INTERACTION_DIAGNOSTIC_STATE.update(
                interaction_id=interaction_id,
                kind=kind,
                started_at=started_at,
                pending=True,
                widget_class=before.get("widget_class", "none"),
            )

        try:
            widget_ref = weakref.ref(widget) if widget is not None else lambda: None
        except TypeError:
            widget_ref = lambda: None

        def report_response():
            current_widget = widget_ref()
            response = _interaction_widget_snapshot(current_widget)
            app = QApplication.instance()
            try:
                active = app.activeWindow() if app is not None else None
                focus = app.focusWidget() if app is not None else None
                response["active_window_class"] = type(active).__name__ if active is not None else "none"
                response["focus_widget_class"] = type(focus).__name__ if focus is not None else "none"
            except RuntimeError:
                response["active_window_class"] = "deleted"
                response["focus_widget_class"] = "deleted"
            response["interaction_id"] = interaction_id
            response["kind"] = kind
            response["response_elapsed_ms"] = round((time.monotonic() - started_at) * 1000)
            response["preview_state"] = _active_preview_interaction_state()
            response["preview_state_changed"] = response["preview_state"] != before_preview_state
            debug_log("interaction-response", "post-event state", force=True, **response)
            with INTERACTION_DIAGNOSTIC_LOCK:
                if INTERACTION_DIAGNOSTIC_STATE.get("interaction_id") == interaction_id:
                    INTERACTION_DIAGNOSTIC_STATE["pending"] = False

        QTimer.singleShot(0, report_response)

        # Media row changes, proxy switches, and audio routing settle after the
        # immediate event-loop turn. Keep two bounded checkpoints only while a
        # preview exists; generic app/debug-window clicks need only the immediate
        # correlated response and should not triple the diagnostics volume.
        def report_stabilized(delay_ms: int):
            elapsed_ms = round((time.monotonic() - started_at) * 1000)
            debug_log(
                "interaction-response",
                "stabilized preview state",
                force=True,
                interaction_id=interaction_id,
                kind=kind,
                checkpoint_ms=delay_ms,
                response_elapsed_ms=elapsed_ms,
                timer_lateness_ms=max(0, elapsed_ms - delay_ms),
                preview_state=_active_preview_interaction_state(),
            )

        try:
            interaction_window = widget.window() if widget is not None else None
            interaction_window_class = (
                type(interaction_window).__name__
                if interaction_window is not None
                else "none"
            )
        except (AttributeError, RuntimeError):
            interaction_window_class = "deleted"

        if before_preview_state != "none" and interaction_window_class != "DebugLogWindow":
            # Wheel/drag input can arrive dozens of times per second. Its
            # immediate response contains the useful scroll/slider value; two
            # extra preview snapshots per event merely load the GUI thread.
            # A release gets one settling sample, while discrete clicks/keys
            # retain both media-start checkpoints.
            if kind in {"wheel", "slider-press", "slider-drag"}:
                checkpoint_delays: Tuple[int, ...] = ()
            elif kind == "slider-release":
                checkpoint_delays = (300,)
            else:
                checkpoint_delays = (300, 1400)

            if checkpoint_delays:
                checkpoint_key = (id(widget), str(kind))
                generation = self.stabilization_generations.get(checkpoint_key, 0) + 1
                self.stabilization_generations[checkpoint_key] = generation
                if len(self.stabilization_generations) > 256:
                    self.stabilization_generations = {checkpoint_key: generation}

                def report_if_current(delay_ms: int):
                    if self.stabilization_generations.get(checkpoint_key) != generation:
                        return
                    report_stabilized(delay_ms)

                for delay_ms in checkpoint_delays:
                    QTimer.singleShot(
                        delay_ms,
                        lambda delay_ms=delay_ms: report_if_current(delay_ms),
                    )
        return True

    def eventFilter(self, obj, event):
        try:
            etype = event.type()
            if etype in (QEvent.KeyPress, QEvent.KeyRelease):
                key_name = _diagnostic_key_name(event)
                mods = event.modifiers()
                close_relevant = key_name in {"Escape", "W", "Q"}
                if close_relevant:
                    WINDOW_DIAGNOSTIC_LAST_INPUT.update(
                        time=time.monotonic(),
                        kind="key",
                        key=key_name,
                        modifiers=str(getattr(mods, "value", mods)),
                        window=_diagnostic_widget_name(getattr(obj, "window", lambda: None)()),
                    )
                interaction_key = _interaction_key_name(event)
                if interaction_key is not None:
                    if _interaction_editor_ancestor(obj) and interaction_key not in {
                        "Enter", "Return", "Escape", "Command+W", "Command+Q"
                    }:
                        interaction_key = None
                if interaction_key is not None:
                    auto_repeat = bool(getattr(event, "isAutoRepeat", lambda: False)())
                    widget = _interaction_semantic_widget(obj)
                    button_space_activation = (
                        isinstance(widget, QAbstractButton)
                        and interaction_key == "Space"
                    )
                    if button_space_activation and etype == QEvent.KeyPress:
                        # Qt activates buttons on Space release. Sampling on
                        # press records the intermediate `down=True` state and
                        # misses the click handler's result entirely.
                        return False
                    if etype == QEvent.KeyRelease and not button_space_activation:
                        return False
                    signature = ("key", self._dense_widget_key(widget), interaction_key)
                    if not auto_repeat or self._dense_event_allowed(signature, 0.2):
                        self._record_interaction(
                            widget,
                            "key-release" if etype == QEvent.KeyRelease else "key-press",
                            event_payload={
                                "key": interaction_key,
                                "auto_repeat": auto_repeat,
                                "modifiers": self._event_modifiers(event),
                            },
                            source_event=event,
                        )
            elif etype in (QEvent.MouseButtonPress, QEvent.MouseMove, QEvent.MouseButtonRelease):
                widget = _interaction_semantic_widget(obj)
                is_slider = isinstance(widget, QAbstractSlider)
                if is_slider and etype == QEvent.MouseButtonPress:
                    kind = "slider-press"
                elif is_slider and etype == QEvent.MouseButtonRelease:
                    kind = "slider-release"
                elif is_slider and etype == QEvent.MouseMove:
                    try:
                        dragging = bool(event.buttons() & Qt.LeftButton) or bool(widget.isSliderDown())
                    except Exception:
                        dragging = False
                    if not dragging or not self._dense_event_allowed(
                        ("slider-drag", self._dense_widget_key(widget)),
                        0.15,
                    ):
                        kind = ""
                    else:
                        kind = "slider-drag"
                elif etype == QEvent.MouseButtonRelease:
                    kind = "mouse-click"
                else:
                    kind = ""
                if kind:
                    mouse_payload = self._mouse_payload(obj, event)
                    mouse_payload["modifiers"] = self._event_modifiers(event)
                    self._record_interaction(
                        widget,
                        kind,
                        event_payload=mouse_payload,
                        source_event=event,
                    )
            elif etype == QEvent.MouseButtonDblClick:
                widget = _interaction_semantic_widget(obj)
                payload = self._mouse_payload(obj, event)
                payload["modifiers"] = self._event_modifiers(event)
                self._record_interaction(
                    widget,
                    "mouse-double-click",
                    event_payload=payload,
                    source_event=event,
                )
            elif etype == QEvent.Wheel:
                widget = _interaction_semantic_widget(obj)
                try:
                    delta = event.angleDelta()
                    horizontal = int(delta.x())
                    vertical = int(delta.y())
                except Exception:
                    horizontal = 0
                    vertical = 0
                direction = (0 if horizontal == 0 else (1 if horizontal > 0 else -1), 0 if vertical == 0 else (1 if vertical > 0 else -1))
                if self._dense_event_allowed(
                    ("wheel", self._dense_widget_key(widget), direction),
                    0.2,
                ):
                    self._record_interaction(
                        widget,
                        "wheel",
                        event_payload={
                            "wheel_x": horizontal,
                            "wheel_y": vertical,
                            "modifiers": self._event_modifiers(event),
                        },
                        source_event=event,
                    )
            elif etype == QEvent.ContextMenu:
                self._record_interaction(
                    _interaction_semantic_widget(obj),
                    "context-menu",
                    event_payload={"modifiers": self._event_modifiers(event)},
                    source_event=event,
                )
            elif etype == QEvent.Drop:
                self._record_interaction(
                    _interaction_semantic_widget(obj),
                    "drop",
                    event_payload={"modifiers": self._event_modifiers(event)},
                    source_event=event,
                )
            elif etype == QEvent.Close and isinstance(obj, QWidget) and obj.isWindow():
                debug_window_close_context(obj, "qt-close-event")
        except Exception:
            pass
        return False


def install_window_diagnostic_filter(app: QApplication):
    global WINDOW_DIAGNOSTIC_FILTER
    if WINDOW_DIAGNOSTIC_FILTER is not None:
        return
    WINDOW_DIAGNOSTIC_FILTER = DiagnosticWindowEventFilter(app)
    app.installEventFilter(WINDOW_DIAGNOSTIC_FILTER)
    debug_log("diagnostic", "interaction and window tracker installed", force=True)


def record_consumed_preview_interaction(widget, event, kind: str, **fields) -> None:
    """Trace an event before LargePreviewDialog intentionally consumes it."""
    tracker = WINDOW_DIAGNOSTIC_FILTER
    if tracker is None:
        return
    payload = dict(fields)
    payload["modifiers"] = tracker._event_modifiers(event)
    if str(kind).startswith(("mouse", "slider")):
        payload.update(tracker._mouse_payload(widget, event))
    try:
        tracker._record_interaction(
            widget,
            kind,
            event_payload=payload,
            source_event=event,
        )
    except TypeError:
        # Small diagnostic adapters (including downstream app/tests) may expose
        # the older three-argument hook. Keep consumed-control tracing useful
        # without forcing those observers to implement event de-duplication.
        try:
            tracker._record_interaction(widget, kind, event_payload=payload)
        except (AttributeError, RuntimeError, TypeError, ValueError):
            return
    except (AttributeError, RuntimeError, ValueError):
        return


def _short_stack_summary(limit: int = 10) -> str:
    try:
        frames = traceback.extract_stack(limit=limit + 4)[:-2]
        useful = []
        for frame in frames[-limit:]:
            useful.append(f"{Path(frame.filename).name}:{frame.lineno}:{frame.name}")
        return " > ".join(useful)
    except Exception:
        return "unavailable"


def debug_window_close_context(widget, label: str):
    """Capture enough context to distinguish native/user/programmatic exits."""
    try:
        app = QApplication.instance()
        now = time.monotonic()
        age = now - float(WINDOW_DIAGNOSTIC_LAST_INPUT.get("time", 0.0) or 0.0)
        recent = WINDOW_DIAGNOSTIC_LAST_INPUT if age <= 2.0 else {}
        focus = app.focusWidget() if app is not None else None
        active = app.activeWindow() if app is not None else None
        debug_log(
            "window-exit",
            "top-level close requested",
            force=True,
            label=label,
            target=_diagnostic_widget_name(widget),
            visible=bool(widget.isVisible()),
            fullscreen=bool(widget.isFullScreen()),
            maximized=bool(widget.windowState() & Qt.WindowMaximized),
            active=_diagnostic_widget_name(active),
            focus=_diagnostic_widget_name(focus),
            recent_input=(f"{recent.get('kind')}:{recent.get('key')} mods={recent.get('modifiers')} age={age:.2f}s" if recent else "none-within-2s"),
            stack=_short_stack_summary(),
        )
    except Exception as exc:
        debug_log("window-exit", "close diagnostic failed", force=True, error=type(exc).__name__)


def _clean_process_diagnostic(text, *paths, limit: int = 1800) -> str:
    """Keep FFmpeg errors useful while removing local file-system paths."""
    value = str(text or "").strip()
    for item in paths:
        if not item:
            continue
        try:
            raw = str(item)
            if raw:
                value = value.replace(raw, "<media>")
        except Exception:
            pass
    value = re.sub(r"https?://[^\s'\"<>]+", "<url>", value, flags=re.IGNORECASE)
    value = re.sub(r"file:(?://)?[^\s'\"<>]+", "<path>", value, flags=re.IGNORECASE)
    value = re.sub(r"[A-Za-z]:\\[^\r\n'\"]+", "<path>", value)
    # Quoted paths can contain spaces; redact them before the conservative
    # unquoted fallback. This keeps copied diagnostics useful without leaking
    # the tail of a selected media filename.
    value = re.sub(
        r"(['\"])/(?:Users|Volumes|private|var|tmp|home)/.*?\1",
        r"\1<path>\1",
        value,
    )
    value = re.sub(r"/(?:Users|Volumes|private|var|tmp|home)/[^\r\n|;,]+", "<path>", value)
    value = " ".join(value.split())
    if len(value) > limit:
        value = value[-limit:]
    return value or "<no stderr>"


def install_qt_media_message_handler():
    """Mirror Qt Multimedia's otherwise-console-only warnings into Debug.

    Some decoder failures never emit ``QMediaPlayer.errorOccurred``.  Qt only
    writes messages such as "Failed to get pixel format" to its logging
    backend, which made the application debugger falsely look clean.  Identical
    messages are aggregated so a broken decoder cannot flood the GUI.
    """
    global QT_MEDIA_MESSAGE_HANDLER_INSTALLED, QT_PREVIOUS_MESSAGE_HANDLER
    if QT_MEDIA_MESSAGE_HANDLER_INSTALLED:
        return

    severity_names = {
        QtMsgType.QtDebugMsg: "debug",
        QtMsgType.QtInfoMsg: "info",
        QtMsgType.QtWarningMsg: "warning",
        QtMsgType.QtCriticalMsg: "critical",
        QtMsgType.QtFatalMsg: "fatal",
    }
    relevant_tokens = (
        "av1",
        "decoder",
        "decoding",
        "ffmpeg",
        "pixel format",
        "current frame",
        "video frame",
        "video sink",
        "playbackengine",
        "multimedia",
    )

    def qt_message_handler(message_type, context, message):
        try:
            category = str(getattr(context, "category", "") or "qt")
            clean_message = _clean_process_diagnostic(message, limit=900)
            normalized = clean_message.casefold()
            relevant = category.startswith("qt.multimedia") or any(
                token in normalized for token in relevant_tokens
            )
            if relevant:
                key = (category, clean_message)
                now = time.monotonic()
                with QT_MEDIA_MESSAGE_LOCK:
                    count, last_emit = QT_MEDIA_MESSAGE_COUNTS.get(key, (0, 0.0))
                    count += 1
                    should_emit = count <= 2 or count in {5, 10, 25, 50, 100} or now - last_emit >= 5.0
                    QT_MEDIA_MESSAGE_COUNTS[key] = (
                        count,
                        now if should_emit else last_emit,
                    )
                    while len(QT_MEDIA_MESSAGE_COUNTS) > 512:
                        QT_MEDIA_MESSAGE_COUNTS.pop(next(iter(QT_MEDIA_MESSAGE_COUNTS)))
                if should_emit:
                    with QT_MEDIA_MESSAGE_LOCK:
                        QT_MEDIA_PENDING_MESSAGES.append(
                            (
                                severity_names.get(message_type, qt_enum_name(message_type)),
                                category,
                                clean_message,
                                count,
                                now,
                            )
                        )
                        while len(QT_MEDIA_PENDING_MESSAGES) > 256:
                            QT_MEDIA_PENDING_MESSAGES.popleft()
        except Exception:
            pass
        previous = QT_PREVIOUS_MESSAGE_HANDLER
        if previous is not None:
            try:
                previous(message_type, context, message)
            except Exception:
                pass
        else:
            # qInstallMessageHandler returns None for Qt's normal default
            # handler. Preserve source-run stderr diagnostics explicitly.
            try:
                sys.stderr.write(str(message).rstrip() + "\n")
            except Exception:
                pass

    try:
        QT_PREVIOUS_MESSAGE_HANDLER = qInstallMessageHandler(qt_message_handler)
        # Retain the Python callable for the lifetime of Qt.
        setattr(DEBUG_BUS, "_qt_media_message_handler", qt_message_handler)
        QT_MEDIA_MESSAGE_HANDLER_INSTALLED = True
    except Exception as exc:
        debug_log(
            "preview-qt",
            "Qt multimedia message capture unavailable",
            force=True,
            error=type(exc).__name__,
        )


install_qt_media_message_handler()


def drain_qt_media_messages():
    """Publish queued Qt backend records on the GUI thread."""
    with QT_MEDIA_MESSAGE_LOCK:
        pending = list(QT_MEDIA_PENDING_MESSAGES)
        QT_MEDIA_PENDING_MESSAGES.clear()
    if not pending:
        return
    owners = []
    for owner in list(VIDEO_PLAYBACK_OWNERS):
        try:
            path = getattr(owner, "current_path", None)
            if path is not None and is_media_path(Path(path)):
                owners.append(owner)
        except (AttributeError, OSError, RuntimeError, TypeError):
            continue
    for severity, category, backend_message, occurrences, _created_at in pending:
        if not owners:
            debug_log(
                "preview-qt",
                "Qt multimedia backend message",
                force=True,
                qt_severity=severity,
                qt_category=category,
                backend_message=backend_message,
                occurrences=occurrences,
            )
            continue
        for owner in owners:
            path = Path(getattr(owner, "current_path"))
            surface = preview_owner_role(owner)
            debug_log(
                "preview-qt",
                "Qt multimedia backend message",
                force=True,
                surface=surface,
                item_id=preview_item_id(path),
                request_id=int(getattr(owner, "playable_proxy_request_id", 0)),
                source_kind=preview_source_kind(owner),
                qt_severity=severity,
                qt_category=category,
                backend_message=backend_message,
                occurrences=occurrences,
            )


def ensure_qt_media_message_drain():
    """Start the main-thread timer after QApplication has been constructed."""
    global QT_MEDIA_MESSAGE_TIMER
    if QT_MEDIA_MESSAGE_TIMER is not None:
        try:
            if QT_MEDIA_MESSAGE_TIMER.isActive():
                return
        except RuntimeError:
            QT_MEDIA_MESSAGE_TIMER = None
    if QApplication.instance() is None:
        return
    timer = QTimer(DEBUG_BUS)
    timer.setInterval(120)
    timer.timeout.connect(drain_qt_media_messages)
    timer.start()
    QT_MEDIA_MESSAGE_TIMER = timer


def invalidate_auxiliary_window_restore(widget: QWidget):
    """Cancel every delayed geometry/fullscreen callback before an auxiliary closes."""
    try:
        setattr(widget, "_folder_manager_restore_generation", int(getattr(widget, "_folder_manager_restore_generation", 0)) + 1)
        setattr(widget, "_folder_manager_close_generation", int(getattr(widget, "_folder_manager_close_generation", 0)) + 1)
        setattr(widget, "_folder_manager_geometry_restore_pending", False)
        setattr(widget, "_folder_manager_fullscreen_cycle", False)
        setattr(widget, "_folder_manager_close_after_expanded_exit", False)
        setattr(widget, "_folder_manager_restore_front_generation", int(getattr(widget, "_folder_manager_restore_front_generation", 0)) + 1)
        timer = getattr(widget, "geometry_save_timer", None)
        if timer is not None:
            timer.stop()
    except (AttributeError, RuntimeError):
        pass


def order_out_auxiliary_native_window(widget: QWidget):
    if sys.platform != "darwin":
        return
    try:
        native = macos_native_window(widget)
        if native is not None:
            native.orderOut_(None)
    except Exception:
        pass


class DebugLogWindow(QDialog):
    def __init__(self, parent=None, owner_window=None, geometry_settings=None):
        # Match Preview: independent native window, explicit logical owner.
        super().__init__(None)
        self.owner_window = top_level_window_for(owner_window or parent)
        if isinstance(geometry_settings, QSettings):
            self._folder_manager_geometry_settings = geometry_settings
        self.setWindowTitle(DEBUG_WINDOW_TITLE)
        self.setWindowFlag(Qt.Window, True)
        # Debug is a disposable auxiliary window. Deleting the Qt object on close
        # also destroys the underlying NSWindow, which prevents a stale Cocoa
        # shell from surviving an expand -> unexpand -> close sequence.
        self.setAttribute(Qt.WA_DeleteOnClose, True)
        self.resize(760, 420)
        layout = QVBoxLayout(self)
        layout.setContentsMargins(12, 12, 12, 12)
        layout.setSpacing(8)

        title = QLabel("Diagnostics Log")
        title.setObjectName("SectionTitle")
        layout.addWidget(title)

        self.log_view = QPlainTextEdit()
        self.log_view.setReadOnly(True)
        self.log_view.setLineWrapMode(QPlainTextEdit.LineWrapMode.NoWrap)
        self.log_view.setMaximumBlockCount(DEBUG_LINE_LIMIT)
        layout.addWidget(self.log_view, stretch=1)

        buttons = QHBoxLayout()
        buttons.addStretch(1)
        self.save_btn = QPushButton("Save Diagnostics…")
        self.copy_btn = QPushButton("Copy Diagnostics")
        self.clear_btn = QPushButton("Clear")
        self.close_btn = QPushButton("Close")
        buttons.addWidget(self.copy_btn)
        buttons.addWidget(self.save_btn)
        buttons.addWidget(self.clear_btn)
        buttons.addWidget(self.close_btn)
        layout.addLayout(buttons)

        self.save_btn.clicked.connect(self.save_log)
        self.copy_btn.clicked.connect(self.copy_log)
        self.clear_btn.clicked.connect(self.clear_log)
        self.close_btn.clicked.connect(self.close)
        self.feedback_timer = QTimer(self)
        self.feedback_timer.setSingleShot(True)
        self.feedback_timer.timeout.connect(self.restore_action_buttons)
        self._pending_log_lines: List[str] = []
        self._log_flush_timer = QTimer(self)
        self._log_flush_timer.setSingleShot(True)
        # Capture every retained line while relayout/repaint happens at a calm,
        # human-readable cadence instead of twenty times per second.
        self._log_flush_timer.setInterval(180)
        self._log_flush_timer.timeout.connect(self.flush_pending_log_lines)
        with DEBUG_LOCK:
            existing_lines = list(DEBUG_LINES)
        if existing_lines:
            # A single document update is dramatically cheaper than repainting
            # and scrolling once per historical line while the window opens.
            self.log_view.setPlainText("\n".join(existing_lines))
            bar = self.log_view.verticalScrollBar()
            bar.setValue(bar.maximum())
        DEBUG_BUS.line.connect(self.append_line)
        configure_settled_window_geometry(self, "debug", QSize(760, 420))

    def append_line(self, line: str):
        self._pending_log_lines.append(str(line))
        if len(self._pending_log_lines) > DEBUG_LINE_LIMIT:
            del self._pending_log_lines[: len(self._pending_log_lines) - DEBUG_LINE_LIMIT]
        if not self._log_flush_timer.isActive():
            self._log_flush_timer.start()

    def flush_pending_log_lines(self):
        if not self._pending_log_lines:
            return
        lines = self._pending_log_lines
        self._pending_log_lines = []
        self.log_view.appendPlainText("\n".join(lines))
        bar = self.log_view.verticalScrollBar()
        bar.setValue(bar.maximum())

    def copy_log(self):
        # Copy the same complete, restart-safe report that Save Diagnostics
        # writes.  A separate preview-only copy button made it needlessly
        # ambiguous which report to send when diagnosing media playback.
        self.copy_btn.setText("Preparing Diagnostics…")
        self.copy_btn.setEnabled(False)
        # The application-wide event filter schedules its correlated
        # interaction response after the click handler. Defer assembly by one
        # complete event-loop turn so the copied report never ends with an
        # apparently hung, unmatched "Copy Diagnostics" input.
        QTimer.singleShot(0, self._queue_copy_after_interaction_response)

    def _queue_copy_after_interaction_response(self):
        QTimer.singleShot(0, self._finish_copy_log)

    def _finish_copy_log(self):
        text = combined_diagnostics_text()
        if not text:
            text = "No diagnostics have been captured yet."
        QApplication.clipboard().setText(text)
        self.copy_btn.setText("Diagnostics Copied")
        self.copy_btn.setEnabled(False)
        self.feedback_timer.start(1200)

    def restore_action_buttons(self):
        for button, text in (
            (getattr(self, "save_btn", None), "Save Diagnostics…"),
            (getattr(self, "copy_btn", None), "Copy Diagnostics"),
        ):
            if button is None:
                continue
            try:
                button.setText(text)
                button.setEnabled(True)
            except RuntimeError:
                pass

    def save_log(self):
        default_name = Path.home() / "Downloads" / f"{SETTINGS_APP} Diagnostics.txt"
        selected, _filter = QFileDialog.getSaveFileName(
            self,
            "Save Diagnostics",
            str(default_name),
            "Text files (*.txt);;All files (*)",
        )
        if not selected:
            return
        text = combined_diagnostics_text()
        try:
            Path(selected).write_text(text + ("\n" if text else ""), encoding="utf-8")
            self.save_btn.setText("Saved")
            self.save_btn.setEnabled(False)
            self.feedback_timer.start(1200)
        except OSError as exc:
            QMessageBox.warning(self, "Could Not Save Diagnostics", str(exc))

    def clear_log(self):
        self._log_flush_timer.stop()
        self._pending_log_lines.clear()
        flush_persistent_diagnostics()
        with DEBUG_LOCK:
            DEBUG_LINES.clear()
            DEBUG_LAST_STATE.clear()
            DEBUG_RATE_LAST.clear()
        try:
            persistent_diagnostic_path().unlink(missing_ok=True)
            persistent_diagnostic_path().with_suffix(".previous.log").unlink(missing_ok=True)
        except OSError:
            pass
        self.log_view.clear()
        debug_log("debug", "cleared")

    def resizeEvent(self, event):
        super().resizeEvent(event)
        schedule_settled_window_geometry_remember(self)

    def moveEvent(self, event):
        super().moveEvent(event)
        schedule_settled_window_geometry_remember(self)

    def showEvent(self, event):
        super().showEvent(event)
        temporarily_attach_window_to_owner_space(self, self.owner_window)
        schedule_macos_native_fullscreen_button(self)

    def changeEvent(self, event):
        if event.type() == QEvent.WindowStateChange:
            debug_log(
                "window-trace",
                "debug WindowStateChange",
                force=True,
                old_state=getattr(event.oldState(), "value", event.oldState()) if hasattr(event, "oldState") else -1,
                qt=_window_forensic_qt_state(self),
            )
        track_standard_fullscreen_change(self, event, "debug")
        if promote_macos_zoom_to_fullscreen(
            self,
            event,
            before_promote=lambda: capture_standard_window_geometry(self, "debug"),
        ):
            event.accept()
            return
        super().changeEvent(event)

    def hideEvent(self, event):
        debug_log(
            "window-trace",
            "debug hideEvent",
            force=True,
            qt=_window_forensic_qt_state(self),
        )
        super().hideEvent(event)

    def closeEvent(self, event):
        debug_window_close_context(self, "debug")
        debug_log(
            "window-trace",
            "debug closeEvent ENTER",
            force=True,
            qt=_window_forensic_qt_state(self),
        )
        if defer_close_until_windowed(self, event, "debug"):
            debug_log(
                "window-trace",
                "debug closeEvent DEFERRED",
                force=True,
                accepted=event.isAccepted(),
                qt=_window_forensic_qt_state(self),
            )
            return
        # Closing after a completed native fullscreen exit is the dangerous case:
        # restoration timers can still be queued even though WindowFullScreen is
        # already clear. Cancel them before Qt hides this top-level window.
        save_window_geometry(self, "debug")
        invalidate_auxiliary_window_restore(self)
        order_out_auxiliary_native_window(self)
        schedule_window_close_forensics(self, "debug-close")
        super().closeEvent(event)
        debug_log(
            "window-trace",
            "debug closeEvent EXIT",
            force=True,
            accepted=event.isAccepted(),
            qt=_window_forensic_qt_state(self),
        )


# ---------------------------------------------------------------------------
# Video surfaces and audio routing


class FrameVideoWidget(QWidget):
    """Paint QVideoSink frames in Qt so pause keeps the exact visible frame.

    QVideoWidget uses a native macOS video layer. That layer can go black when
    paused, lose stacking against overlays, and leak across Spaces. A QVideoSink
    gives us the decoded frame while this ordinary QWidget keeps painting the
    last one until a newer frame arrives.
    """

    firstFrameReady = Signal()
    frameConversionUnavailable = Signal(str)

    def __init__(
        self,
        parent=None,
        target_fps: Optional[float] = None,
        retain_source_resolution: bool = False,
    ):
        super().__init__(parent)
        self.video_sink = QVideoSink(self) if QVideoSink is not None else None
        self._frame_image = None
        self._poster_image = None
        self._pending_frame = None
        self._paused = False
        self._reported_frame = False
        self._initial_frame_attempted = False
        self._frames_received = 0
        self._frames_converted = 0
        self._frames_conversion_null = 0
        self._frames_conversion_error = 0
        self._frames_coalesced = 0
        self._last_frame_received_at = 0.0
        # QVideoSink can deliver queued frames after QMediaPlayer.stop() or a
        # source swap. Keep an explicit generation so an old decoder can never
        # repaint a stopped surface or satisfy the next video's first-frame
        # watchdog.
        self._frame_generation = 0
        self._accept_frames = True
        self._requested_target_fps = float(target_fps) if target_fps is not None else None
        self._retain_source_resolution = bool(retain_source_resolution)
        self._frame_interval_ms = 17
        self._last_refresh_probe_monotonic = 0.0
        self._last_frame_flush_monotonic = 0.0
        self._native_video_widget = None
        self._native_pause_overlay = None
        self._native_fallback_active = False
        # QVideoWidget owns a native Cocoa video layer on macOS. Native layers
        # are not clipped reliably by QStackedWidget: after a source/page
        # change they can remain black above unrelated controls and even leak
        # across Spaces. Keep Darwin on the ordinary QVideoSink surface and
        # use the cached compatibility proxy only when frame conversion fails.
        if QVideoWidget is not None and sys.platform != "darwin":
            try:
                self._native_video_widget = QVideoWidget(self)
                self._native_video_widget.setObjectName("NativeVideoFallback")
                # QVideoWidget owns a native macOS video layer.  An overlay
                # painted by FrameVideoWidget is therefore underneath it.  A
                # child of the native surface remains above the movie and gives
                # fallback codecs (notably WebM/VP9) the same paused treatment
                # as ordinary QVideoSink playback.
                self._native_pause_overlay = QLabel("-paused-", self._native_video_widget)
                self._native_pause_overlay.setObjectName("PausedOverlay")
                self._native_pause_overlay.setAlignment(Qt.AlignCenter)
                self._native_pause_overlay.setAttribute(Qt.WA_TransparentForMouseEvents, True)
                self._native_pause_overlay.setStyleSheet(PAUSED_OVERLAY_STYLE)
                self._native_pause_overlay.hide()
                self._native_video_widget.hide()
            except Exception:
                self._native_video_widget = None
                self._native_pause_overlay = None
        self._refresh_frame_interval()
        self._frame_flush_timer = QTimer(self)
        self._frame_flush_timer.setSingleShot(True)
        self._frame_flush_timer.setTimerType(Qt.PreciseTimer)
        self._frame_flush_timer.timeout.connect(self._flush_pending_frame)
        self.setAttribute(Qt.WA_OpaquePaintEvent, True)
        self.setAutoFillBackground(False)
        if self.video_sink is not None:
            generation = self._frame_generation
            self.video_sink.videoFrameChanged.connect(
                lambda frame, token=generation: self._accept_video_frame(frame, token)
            )

    def reset_player_output(self, player):
        """Return playback to the ordinary QVideoSink surface for a new file."""
        if player is None or QVideoSink is None:
            return
        old_sink = self.video_sink
        # A timer may still hold a frame from the previous decoder even after
        # its signal connection has been replaced. Drop that work first.
        self._frame_flush_timer.stop()
        self._pending_frame = None
        self._frame_generation += 1
        generation = self._frame_generation
        try:
            replacement_sink = QVideoSink(self)
            replacement_sink.videoFrameChanged.connect(
                lambda frame, token=generation: self._accept_video_frame(frame, token)
            )
            self.video_sink = replacement_sink
        except Exception:
            self.video_sink = old_sink
            return
        try:
            player.setVideoSink(self.video_sink)
        except Exception:
            try:
                player.setVideoOutput(None)
                player.setVideoSink(self.video_sink)
            except Exception:
                self.video_sink = old_sink
                try:
                    replacement_sink.deleteLater()
                except (AttributeError, RuntimeError):
                    pass
                return
        self._accept_frames = True
        if old_sink is not None and old_sink is not self.video_sink:
            try:
                old_sink.deleteLater()
            except RuntimeError:
                pass
        self._native_fallback_active = False
        if self._native_pause_overlay is not None:
            self._native_pause_overlay.hide()
        if self._native_video_widget is not None:
            self._native_video_widget.hide()
        self.update()

    def activate_native_fallback(self, player, reason: str = "no convertible video frame") -> bool:
        """Use Qt's direct video surface when QVideoFrame.toImage cannot render a codec.

        WebM/VP9 and a few hardware pixel formats can decode successfully in Qt's
        FFmpeg backend while QVideoSink -> QImage conversion still yields a null
        image on macOS. QVideoWidget renders those decoded frames directly instead
        of falling back to a static thumbnail.
        """
        if player is None or self._native_video_widget is None:
            return False
        if self._native_fallback_active:
            return True
        try:
            player.setVideoOutput(self._native_video_widget)
            self._native_video_widget.setGeometry(self.rect())
            self._native_video_widget.show()
            self._native_video_widget.raise_()
            self._native_fallback_active = True
            self._sync_native_pause_overlay()
            self._refresh_paused_native_frame(player)
            debug_log("media", "direct video fallback enabled", force=True, reason=reason)
            return True
        except Exception as exc:
            debug_log("media", "direct video fallback unavailable", error=type(exc).__name__)
            return False

    def using_native_fallback(self) -> bool:
        return bool(self._native_fallback_active)

    def _sync_native_pause_overlay(self):
        overlay = self._native_pause_overlay
        surface = self._native_video_widget
        if overlay is None or surface is None:
            return
        overlay.setGeometry(surface.rect())
        visible = bool(self._native_fallback_active and self._paused)
        overlay.setVisible(visible)
        if visible:
            overlay.raise_()

    def _refresh_paused_native_frame(self, player):
        """Ask a newly-bound native surface to render the current paused frame.

        Rebinding a player that is already paused often leaves QVideoWidget
        black until its next seek.  A one-millisecond seek and restore triggers
        decoding without changing the user's logical playback state or visible
        timeline position.
        """
        if not self._paused or player is None:
            return
        try:
            position = max(0, int(player.position()))
            duration = max(0, int(player.duration()))
        except (AttributeError, RuntimeError, TypeError, ValueError):
            return

        target = position + 1 if duration <= 0 or position < duration else max(0, position - 1)

        def nudge():
            if not self._native_fallback_active or not self._paused:
                return
            try:
                player.setPosition(target)
                if target != position:
                    QTimer.singleShot(0, lambda: self._restore_native_position(player, position))
            except (AttributeError, RuntimeError):
                pass

        QTimer.singleShot(0, nudge)

    def _restore_native_position(self, player, position: int):
        if not self._native_fallback_active or not self._paused:
            return
        try:
            player.setPosition(position)
        except (AttributeError, RuntimeError, TypeError):
            pass

    def _refresh_frame_interval(self):
        target_fps = self._requested_target_fps
        if target_fps is None:
            screen = self.screen()
            target_fps = float(screen.refreshRate()) if screen is not None else 60.0
            # Full-size previews normally track a ProMotion display.  While a
            # scanner is streaming rows, 30 fps leaves regular GUI slices for
            # selection, list insertion, and controls; it returns to the display
            # cadence automatically on the next one-second refresh probe.
            if scanner_work_active():
                target_fps = min(target_fps, 30.0)
        if target_fps != target_fps or target_fps <= 1.0 or target_fps > 1000.0:
            target_fps = 60.0
        self._frame_interval_ms = max(1, round(1000.0 / target_fps))
        self._last_refresh_probe_monotonic = time.monotonic()

    def _accept_video_frame(self, frame, generation: Optional[int] = None):
        # Decoders can deliver 4K frames at 60+ fps. Converting every frame to a
        # QImage on Qt's GUI thread stalls selection, scrubbing, and window input.
        # Retain only the newest frame and paint at a display-appropriate rate.
        if not self._accept_frames:
            return
        if generation is not None and generation != self._frame_generation:
            return
        # Qt sends an invalid frame when a source is cleared or reaches its
        # end. It is a transport notification, not a failed image conversion.
        # Do not replace a pending real frame or trigger proxy recovery for it.
        if hasattr(frame, "isValid") and not frame.isValid():
            return
        now = time.monotonic()
        self._frames_received += 1
        self._last_frame_received_at = now
        if self._pending_frame is not None:
            self._frames_coalesced += 1
        self._pending_frame = frame
        if (
            self._requested_target_fps is None
            and now - self._last_refresh_probe_monotonic >= 1.0
        ):
            self._refresh_frame_interval()
        if not self._initial_frame_attempted:
            self._flush_pending_frame()
            return
        if self._frame_flush_timer.isActive():
            return
        elapsed_ms = (now - self._last_frame_flush_monotonic) * 1000.0
        remaining_ms = self._frame_interval_ms - elapsed_ms
        if remaining_ms <= 0:
            self._flush_pending_frame()
        else:
            self._frame_flush_timer.start(max(1, round(remaining_ms)))

    def _flush_pending_frame(self):
        frame = self._pending_frame
        self._pending_frame = None
        if frame is None:
            return
        self._initial_frame_attempted = True
        try:
            image = frame.toImage()
        except Exception as exc:
            self._frames_conversion_error += 1
            debug_log("media", "video frame conversion failed", error=type(exc).__name__)
            if not self._reported_frame:
                self.frameConversionUnavailable.emit("frame conversion failed")
            return
        if image.isNull():
            self._frames_conversion_null += 1
            if not self._reported_frame:
                self.frameConversionUnavailable.emit("decoded frame is not convertible")
            return
        if not self._retain_source_resolution and self.width() > 0 and self.height() > 0 and (
            image.width() > self.width() or image.height() > self.height()
        ):
            mode = Qt.SmoothTransformation if self._paused else Qt.FastTransformation
            image = image.scaled(self.size(), Qt.KeepAspectRatio, mode)
        self._frame_image = image
        self._frames_converted += 1
        self._last_frame_flush_monotonic = time.monotonic()
        self.update()
        if not self._reported_frame:
            self._reported_frame = True
            self.firstFrameReady.emit()

    def set_poster_pixmap(self, pixmap: QPixmap):
        self._poster_image = None if pixmap.isNull() else pixmap.toImage()
        self.update()

    def clear_frame(self, clear_poster: bool = False):
        self._accept_frames = False
        self._frame_generation += 1
        self._frame_flush_timer.stop()
        self._pending_frame = None
        self._frame_image = None
        self._reported_frame = False
        self._initial_frame_attempted = False
        self._last_frame_flush_monotonic = 0.0
        self._frames_received = 0
        self._frames_converted = 0
        self._frames_conversion_null = 0
        self._frames_conversion_error = 0
        self._frames_coalesced = 0
        self._last_frame_received_at = 0.0
        if clear_poster:
            self._poster_image = None
        self.update()

    def has_frame(self) -> bool:
        return self._frame_image is not None and not self._frame_image.isNull()

    def has_poster(self) -> bool:
        return self._poster_image is not None and not self._poster_image.isNull()

    def has_visual(self) -> bool:
        """Return whether this surface can paint a real frame or poster."""
        return self.has_frame() or self.has_poster()

    def visual_pixmap(self) -> QPixmap:
        """Copy the currently paintable visual for a paired preview surface."""
        image = self._frame_image if self.has_frame() else self._poster_image
        if image is None or image.isNull():
            return QPixmap()
        return QPixmap.fromImage(image)

    def frame_diagnostics(self) -> Dict[str, object]:
        """Return silent per-source counters for terminal preview diagnostics."""
        age_ms = (
            max(0, round((time.monotonic() - self._last_frame_received_at) * 1000.0))
            if self._last_frame_received_at > 0.0
            else -1
        )
        return {
            "frames_received": int(self._frames_received),
            "frames_converted": int(self._frames_converted),
            "frames_conversion_null": int(self._frames_conversion_null),
            "frames_conversion_error": int(self._frames_conversion_error),
            "frames_coalesced": int(self._frames_coalesced),
            "last_frame_age_ms": age_ms,
        }

    def set_paused(self, paused: bool):
        paused = bool(paused)
        if paused and self._pending_frame is not None:
            self._frame_flush_timer.stop()
            self._flush_pending_frame()
        self._paused = paused
        self._sync_native_pause_overlay()
        # Repaint even when the logical state is unchanged. macOS can discard a
        # child widget backing store while switching Spaces; activation then
        # reasserts the state and this redraw restores the retained frame/badge.
        self.update()

    def paintEvent(self, _event):
        painter = QPainter(self)
        painter.fillRect(self.rect(), QColor(PREVIEW_CANVAS_COLOR))
        image = self._frame_image if self._frame_image is not None else self._poster_image
        if image is not None and not image.isNull() and self.width() > 0 and self.height() > 0:
            source_width = max(1, image.width())
            source_height = max(1, image.height())
            scale = min(self.width() / source_width, self.height() / source_height)
            width = max(1, round(source_width * scale))
            height = max(1, round(source_height * scale))
            target = QRect((self.width() - width) // 2, (self.height() - height) // 2, width, height)
            painter.setRenderHint(QPainter.SmoothPixmapTransform, self._paused)
            painter.drawImage(target, image)
        # A pause badge describes a frozen visual, not a loading state.  Drawing
        # it over an empty black surface made failed/loading previews look as if
        # a playable frame existed and duplicated the preparation text.
        if self._paused and image is not None and not image.isNull():
            painter.fillRect(self.rect(), QColor(0, 0, 0, 105))
            font = painter.font()
            font.setBold(True)
            font.setPointSize(max(13, min(22, self.height() // 8)))
            painter.setFont(font)
            painter.setPen(QColor("#ffffff"))
            painter.drawText(self.rect(), Qt.AlignCenter, "-paused-")

    def resizeEvent(self, event):
        super().resizeEvent(event)
        if self._native_video_widget is not None:
            self._native_video_widget.setGeometry(self.rect())
            self._sync_native_pause_overlay()

    def showEvent(self, event):
        super().showEvent(event)
        if self._native_video_widget is not None and self._native_fallback_active:
            self._native_video_widget.setGeometry(self.rect())
            self._native_video_widget.show()
            self._native_video_widget.raise_()
            self._sync_native_pause_overlay()
        if self._requested_target_fps is None:
            self._refresh_frame_interval()
        # Restore the retained frame immediately after a macOS Space/window
        # transition instead of waiting for another decoded frame to arrive.
        self.update()


class AspectPixmapLabel(QLabel):
    """Paint a pixmap to the available area without contributing its pixel size.

    QLabel's default size hint follows the pixmap dimensions. Loading artwork
    while the preview is fullscreen therefore made the hidden stacked page ask
    for a fullscreen-sized normal window, defeating the cinema restore geometry.
    """

    def __init__(self, parent=None):
        super().__init__(parent)
        self._source_pixmap = QPixmap()
        self.setSizePolicy(QSizePolicy.Ignored, QSizePolicy.Ignored)
        self.setMinimumSize(0, 0)

    def setPixmap(self, pixmap: QPixmap):
        self._source_pixmap = QPixmap(pixmap) if pixmap is not None else QPixmap()
        self.update()

    def clear(self):
        self._source_pixmap = QPixmap()
        self.update()

    def sizeHint(self):
        return QSize(640, 420)

    def minimumSizeHint(self):
        return QSize(0, 0)

    def paintEvent(self, event):
        if self._source_pixmap.isNull():
            super().paintEvent(event)
            return
        painter = QPainter(self)
        painter.fillRect(self.rect(), QColor("#000000"))
        target = self._source_pixmap.size()
        target.scale(self.size(), Qt.KeepAspectRatio)
        rect = QRect(
            (self.width() - target.width()) // 2,
            (self.height() - target.height()) // 2,
            target.width(),
            target.height(),
        )
        painter.setRenderHint(QPainter.SmoothPixmapTransform, True)
        painter.drawPixmap(rect, self._source_pixmap)


def follow_system_audio_output(owner: QObject, audio_output) -> Optional[QObject]:
    """Keep Qt playback routed to the output currently selected by macOS."""
    if QMediaDevices is None or audio_output is None:
        return None
    devices = QMediaDevices(owner)

    def sync_default_output():
        try:
            device = QMediaDevices.defaultAudioOutput()
            if device.isNull():
                debug_log(
                    "media-preview",
                    "system audio output unavailable",
                    force=True,
                    surface=str(getattr(owner, "preview_surface_role", "unknown")),
                    **audio_output_snapshot(audio_output),
                )
                return
            if audio_output.device() != device:
                muted = audio_output.isMuted()
                volume = audio_output.volume()
                audio_output.setDevice(device)
                audio_output.setVolume(volume)
                audio_output.setMuted(muted)
                debug_log(
                    "media-preview",
                    "preview audio route followed system default",
                    force=True,
                    surface=str(getattr(owner, "preview_surface_role", "unknown")),
                    **audio_output_snapshot(audio_output),
                )
        except (AttributeError, RuntimeError) as exc:
            debug_log(
                "media-preview",
                "preview audio route synchronization failed",
                force=True,
                surface=str(getattr(owner, "preview_surface_role", "unknown")),
                error=type(exc).__name__,
            )

    sync_default_output()
    devices.audioOutputsChanged.connect(sync_default_output)
    setattr(owner, "_sync_default_audio_output", sync_default_output)
    return devices


def show_debug_window(parent=None):
    global DEBUG_WINDOW
    ensure_qt_media_message_drain()

    def make_window():
        window = DebugLogWindow(
            None,
            owner_window=parent,
            geometry_settings=window_geometry_settings(parent) if isinstance(parent, QWidget) else None,
        )

        def forget_this_window(*_args):
            global DEBUG_WINDOW
            if DEBUG_WINDOW is window:
                DEBUG_WINDOW = None

        window.destroyed.connect(forget_this_window)
        return window

    try:
        if DEBUG_WINDOW is None or not DEBUG_WINDOW.isVisible():
            DEBUG_WINDOW = make_window()
        else:
            DEBUG_WINDOW.owner_window = top_level_window_for(parent)
        DEBUG_WINDOW.show()
        temporarily_attach_window_to_owner_space(DEBUG_WINDOW, DEBUG_WINDOW.owner_window)
        DEBUG_WINDOW.raise_()
        DEBUG_WINDOW.activateWindow()
    except RuntimeError:
        DEBUG_WINDOW = make_window()
        DEBUG_WINDOW.show()
    log_preview_diagnostic_session()
    debug_log("debug", "window opened")
    return DEBUG_WINDOW


def log_preview_diagnostic_session():
    """Record runtime and currently active players whenever Debug is opened."""
    debug_log(
        "media-preview",
        "preview diagnostic session opened",
        force=True,
        app=SETTINGS_APP,
        shared_version=APP_VERSION,
        qt_version=qVersion(),
        platform=sys.platform,
        architecture=(os.uname().machine if hasattr(os, "uname") else "unknown"),
        frozen=bool(getattr(sys, "frozen", False)),
        multimedia_available=MEDIA_PREVIEW_AVAILABLE,
        ffmpeg_available=bool(ffmpeg_path()),
        ffprobe_available=bool(ffprobe_path()),
        qt_media_backend=os.environ.get("QT_MEDIA_BACKEND", "default"),
        qt_hw_decoder_types=os.environ.get("QT_FFMPEG_DECODING_HW_DEVICE_TYPES", "default"),
        qt_hw_texture_conversion=os.environ.get("QT_DISABLE_HW_TEXTURES_CONVERSION", "default"),
    )
    for owner in list(VIDEO_PLAYBACK_OWNERS):
        try:
            path = getattr(owner, "current_path", None)
            if path is None:
                continue
            player = getattr(owner, "media_player", None)
            widget = getattr(owner, "video_widget", None)
            surface = preview_owner_role(owner)
            status = qt_enum_name(player.mediaStatus()) if player is not None else "unavailable"
            state = qt_enum_name(player.playbackState()) if player is not None else "unavailable"
            snapshot_fields = dict(getattr(owner, "_debug_media_descriptor", {}) or {})
            snapshot_fields.update(preview_surface_snapshot(owner))
            try:
                logical_paused = bool(owner.logical_playback_paused())
            except (AttributeError, RuntimeError):
                logical_paused = bool(getattr(owner, "playback_paused_by_user", False))
            preview_trace(
                surface,
                "active preview snapshot",
                Path(path),
                force=True,
                request_id=int(getattr(owner, "playable_proxy_request_id", 0)),
                source_kind=preview_source_kind(owner),
                media_status=status,
                playback_state=state,
                logical_paused=logical_paused,
                has_frame=bool(widget is not None and widget.has_frame()),
                has_poster=bool(
                    widget is not None
                    and getattr(widget, "_poster_image", None) is not None
                    and not widget._poster_image.isNull()
                ),
                **snapshot_fields,
            )
        except (AttributeError, RuntimeError, TypeError, ValueError):
            continue


# ---------------------------------------------------------------------------
# Playback ownership and native window integration


def application_is_active() -> bool:
    app = QApplication.instance()
    if app is None:
        return True
    try:
        state = app.applicationState()
        active_state = Qt.ApplicationState.ApplicationActive
    except Exception:
        try:
            state = app.applicationState()
            active_state = Qt.ApplicationActive
        except Exception:
            return True
    return state == active_state


def register_video_owner(owner: object):
    ensure_qt_media_message_drain()
    if owner not in VIDEO_PLAYBACK_OWNERS:
        VIDEO_PLAYBACK_OWNERS.append(owner)


def unregister_video_owner(owner: object):
    if owner in VIDEO_PLAYBACK_OWNERS:
        VIDEO_PLAYBACK_OWNERS.remove(owner)


def request_video_playback(owner: object):
    """Grant playback while enforcing one large-window owner globally.

    A visible Space-triggered/scanner Preview is authoritative.  Embedded
    panels may mirror its selection, but they are never permitted to start a
    second decoder or audio route until every large Preview is closed.
    """
    role = str(getattr(owner, "preview_surface_role", ""))
    if role == "window" and hasattr(owner, "global_playback_lock_owners"):
        # A window reaching this function is explicitly claiming playback
        # (opening, navigating, or a user transport action). Transfer authority
        # from any older window lock without changing either window's saved
        # user pause preference.
        owner.global_playback_lock_owners = []
    if role == "embedded":
        blocker = visible_large_preview_owner(excluding=owner)
        if blocker is not None:
            pause = getattr(owner, "pause_video_preview", None)
            if callable(pause):
                pause()
            preview_trace(
                "embedded",
                "playback ownership denied",
                getattr(owner, "current_path", None),
                force=True,
                decision="a visible Preview window owns all media playback",
                blocking_surface=type(blocker).__name__,
                **preview_surface_snapshot(owner),
            )
            return False
    for other in list(VIDEO_PLAYBACK_OWNERS):
        if other is owner:
            continue
        # Constructors register surfaces before they are shown or assigned a
        # row. A live embedded player must not "pause" such an empty future
        # Preview and accidentally turn its default autoplay preference off.
        if getattr(other, "current_path", None) is None:
            continue
        if preview_owner_role(other) == "window":
            try:
                if not other.isVisible():
                    continue
            except (AttributeError, RuntimeError):
                continue
        if role == "window":
            suspend = getattr(other, "suspend_for_large_preview", None)
            if callable(suspend):
                suspend(owner)
                continue
        pause = getattr(other, "pause_video_preview", None)
        if callable(pause):
            pause()
    return True


def preview_owner_role(owner: object) -> str:
    role = str(getattr(owner, "preview_surface_role", "") or "").strip().casefold()
    if role:
        return role
    return "embedded" if type(owner).__name__ == "PreviewPanel" else "window"


def visible_large_preview_owner(excluding=None):
    for candidate in list(VIDEO_PLAYBACK_OWNERS):
        if candidate is excluding or preview_owner_role(candidate) != "window":
            continue
        try:
            if candidate.isVisible() and getattr(candidate, "current_path", None) is not None:
                return candidate
        except (AttributeError, RuntimeError):
            continue
    return None


def macos_native_window(widget: QWidget):
    """Return the NSWindow backing a Qt widget when PyObjC is available."""
    app = QApplication.instance()
    if (
        sys.platform != "darwin"
        or app is None
        or QApplication.platformName().casefold() != "cocoa"
        or not widget.isWindow()
        or QThread.currentThread() is not app.thread()
    ):
        return None
    try:
        import objc

        # PyObjC expects the integer address carried by Qt's WId. Wrapping it in
        # ctypes.c_void_p first creates a pointer-to-pointer style conversion on
        # some PyObjC/Python combinations and can hand AppKit an invalid view.
        native_id = int(widget.winId())
        if native_id <= 0:
            return None
        native_view = objc.objc_object(c_void_p=native_id)
        return native_view.window()
    except Exception as exc:
        if not bool(getattr(widget, "_macos_native_window_error_logged", False)):
            setattr(widget, "_macos_native_window_error_logged", True)
            debug_log(
                "window",
                "native macOS window unavailable; using Qt fallback",
                force=True,
                widget=widget.__class__.__name__,
                error=type(exc).__name__,
            )
        return None


def _window_forensic_qt_state(widget: QWidget) -> str:
    try:
        state = widget.windowState()
        geom = widget.geometry()
        return (
            f"class={widget.__class__.__name__},title={widget.windowTitle()!r},"
            f"visible={widget.isVisible()},hidden={widget.isHidden()},"
            f"fullscreen={bool(state & Qt.WindowFullScreen)},maximized={bool(state & Qt.WindowMaximized)},"
            f"minimized={bool(state & Qt.WindowMinimized)},"
            f"geom={geom.x()},{geom.y()},{geom.width()}x{geom.height()},winid={int(widget.winId())}"
        )
    except Exception as exc:
        return f"qt-state-error={type(exc).__name__}"


def log_window_forensic_inventory(label: str, expected_title: str = "", expected_number: int = -1):
    """Snapshot Qt + AppKit top-level windows after a suspicious close.

    This deliberately does not retain the closing QWidget, so the diagnostic
    itself cannot keep the window alive and mask the orphan-shell bug.
    """
    app = QApplication.instance()
    qt_bits = []
    if app is not None:
        try:
            for window in app.topLevelWidgets():
                try:
                    title = str(window.windowTitle() or "")
                    if window.isVisible() or "Debug" in title or "Preview" in title or "Scan" in title:
                        qt_bits.append(_window_forensic_qt_state(window))
                except RuntimeError:
                    continue
        except Exception as exc:
            qt_bits.append(f"qt-inventory-error={type(exc).__name__}")
    debug_log(
        "window-trace",
        "qt top-level inventory",
        force=True,
        phase=label,
        windows=" || ".join(qt_bits) if qt_bits else "none",
    )

    if sys.platform != "darwin":
        return
    try:
        from AppKit import NSApp
        native_bits = []
        expected_bits = []
        for native in list(NSApp.windows() or []):
            try:
                number = int(native.windowNumber())
                title = str(native.title() or "")
                frame = native.frame()
                content = native.contentView()
                content_class = type(content).__name__ if content is not None else "None"
                bit = (
                    f"num={number},title={title!r},visible={bool(native.isVisible())},"
                    f"key={bool(native.isKeyWindow())},main={bool(native.isMainWindow())},"
                    f"onscreen={bool(native.isOnActiveSpace()) if hasattr(native, 'isOnActiveSpace') else 'na'},"
                    f"alpha={float(native.alphaValue()):.2f},style={int(native.styleMask())},"
                    f"collection={int(native.collectionBehavior())},"
                    f"frame={float(frame.origin.x):.0f},{float(frame.origin.y):.0f},"
                    f"{float(frame.size.width):.0f}x{float(frame.size.height):.0f},content={content_class}"
                )
                if number == int(expected_number) or (expected_title and title == expected_title):
                    expected_bits.append(bit)
                if native.isVisible() or number == int(expected_number) or "Debug" in title or "Preview" in title or "Scan" in title:
                    native_bits.append(bit)
            except Exception as exc:
                native_bits.append(f"native-entry-error={type(exc).__name__}")
        debug_log(
            "window-trace",
            "appkit window inventory",
            force=True,
            phase=label,
            expected_number=expected_number,
            expected=" || ".join(expected_bits) if expected_bits else "NOT_FOUND",
            windows=" || ".join(native_bits) if native_bits else "none",
        )
    except Exception as exc:
        debug_log(
            "window-trace",
            "appkit inventory failed",
            force=True,
            phase=label,
            error=f"{type(exc).__name__}: {exc}",
        )


def schedule_window_close_forensics(widget: QWidget, label: str):
    """Record native close forensics only when explicitly requested.

    Set FM_WINDOW_FORENSICS=1 before launch when a ghost-window investigation is
    needed. Normal Debug logs stay readable instead of collecting full AppKit and
    Qt window inventories on every close.
    """
    if os.environ.get("FM_WINDOW_FORENSICS", "").strip().lower() not in {"1", "true", "yes", "on"}:
        return
    try:
        title = str(widget.windowTitle() or "")
    except Exception:
        title = ""
    native_number = -1
    try:
        native = macos_native_window(widget)
        if native is not None:
            native_number = int(native.windowNumber())
    except Exception:
        pass
    debug_log(
        "window-trace",
        "close forensic armed",
        force=True,
        phase=label,
        expected_title=title,
        expected_number=native_number,
        qt=_window_forensic_qt_state(widget),
    )
    for delay in (0, 350, 1200, 3500):
        QTimer.singleShot(
            delay,
            lambda d=delay, ttl=title, num=native_number, tag=label:
                log_window_forensic_inventory(f"{tag} +{d}ms", ttl, num),
        )


def install_macos_native_fullscreen_button(widget: QWidget) -> bool:
    """Make the green traffic-light button call NSWindow fullscreen directly.

    Converting Qt's already-started maximize transition in WindowStateChange leaves
    two Cocoa animations alive. Their delayed completions can then alternate a
    window between maximized and fullscreen long after the original click. Wiring
    the native button before it is clicked gives the transition a single owner.
    """
    if sys.platform != "darwin":
        return False
    # Cocoa may replace the title-bar zoom button after a fullscreen/content
    # transition. Rebind the *current* button every time instead of trusting a
    # stale Python flag that refers to an older native control.
    try:
        from AppKit import (
            NSWindowCollectionBehaviorFullScreenPrimary,
            NSWindowZoomButton,
        )

        window = macos_native_window(widget)
        if window is None:
            return False
        behavior = window.collectionBehavior()
        window.setCollectionBehavior_(
            behavior | NSWindowCollectionBehaviorFullScreenPrimary
        )
        button = window.standardWindowButton_(NSWindowZoomButton)
        if button is None:
            return False
        button.setTarget_(window)
        button.setAction_("toggleFullScreen:")
        try:
            native_identity = (int(window.windowNumber()), int(button.hash()))
        except Exception:
            native_identity = (id(window), id(button))
        previous_identity = getattr(widget, "_macos_native_fullscreen_button_identity", None)
        setattr(widget, "_macos_native_fullscreen_button_identity", native_identity)
        setattr(widget, "_macos_native_fullscreen_button", True)
        if previous_identity != native_identity:
            debug_log(
                "window",
                "native macOS fullscreen button installed",
                force=True,
                widget=widget.__class__.__name__,
            )
        return True
    except Exception as exc:
        if not bool(getattr(widget, "_macos_native_fullscreen_button_error_logged", False)):
            setattr(widget, "_macos_native_fullscreen_button_error_logged", True)
            debug_log(
                "window",
                "native macOS fullscreen button install failed; using Qt fallback",
                force=True,
                widget=widget.__class__.__name__,
                error=type(exc).__name__,
            )
        return False


def toggle_macos_native_fullscreen(widget: QWidget) -> bool:
    """Request one native macOS fullscreen transition without changing Qt state."""
    if not install_macos_native_fullscreen_button(widget):
        return False
    try:
        window = macos_native_window(widget)
        if window is None:
            return False
        window.toggleFullScreen_(None)
        return True
    except Exception as exc:
        debug_log(
            "window",
            "native macOS fullscreen request failed; using Qt fallback",
            force=True,
            widget=widget.__class__.__name__,
            error=type(exc).__name__,
        )
        return False


def schedule_macos_native_fullscreen_button(widget: QWidget):
    if sys.platform != "darwin":
        return
    try:
        if not widget.isVisible():
            return
    except RuntimeError:
        return
    guarded = weakref.ref(widget)

    def install_if_alive():
        candidate = guarded()
        if candidate is None:
            return
        try:
            if candidate.isVisible():
                install_macos_native_fullscreen_button(candidate)
        except RuntimeError:
            return

    for delay in (0, 120, 450, 1200):
        QTimer.singleShot(delay, install_if_alive)


def promote_macos_zoom_to_fullscreen(
    widget: QWidget,
    event,
    enter_fullscreen: Optional[Callable[[], None]] = None,
    before_promote: Optional[Callable[[], None]] = None,
) -> bool:
    """On macOS, make the green zoom button behave as fullscreen for this app."""
    if sys.platform != "darwin" or event.type() != QEvent.WindowStateChange:
        return False
    # Normally the native green button is rewired before the first click, so Qt
    # never enters WindowMaximized. Keep this conversion only for environments
    # where PyObjC/native access is unavailable (including some frozen builds).
    # Do not trust the cached "installed" flag here. Cocoa may recreate the
    # title-bar zoom button after it was wired, and a real WindowMaximized event
    # is definitive evidence that the click behaved as zoom rather than fullscreen.
    if bool(getattr(widget, "_macos_fullscreen_promotion_pending", False)):
        return True
    try:
        old_state = event.oldState()
    except Exception:
        old_state = Qt.WindowStates()
    if old_state & Qt.WindowFullScreen:
        return False
    state = widget.windowState()
    if state & Qt.WindowMaximized and not (state & Qt.WindowFullScreen):
        # Clearing the maximized flag below can synchronously deliver another
        # WindowStateChange on Cocoa. Mark the transaction first so that nested
        # event cannot schedule a duplicate fullscreen request.
        setattr(widget, "_macos_fullscreen_promotion_pending", True)
        if before_promote is not None:
            before_promote()
        debug_log(
            "input",
            "macOS green button requested fullscreen",
            force=True,
            widget=widget.__class__.__name__,
            old_state=str(old_state),
            new_state=str(state),
            x=widget.x(),
            y=widget.y(),
            width=widget.width(),
            height=widget.height(),
        )
        action = enter_fullscreen or widget.showFullScreen

        def finish_promotion():
            try:
                state_now = widget.windowState()
                if not (state_now & Qt.WindowMaximized) or state_now & Qt.WindowFullScreen:
                    return
                action()
                debug_log(
                    "response",
                    "window entered fullscreen",
                    force=True,
                    widget=widget.__class__.__name__,
                    full=widget.isFullScreen(),
                    width=widget.width(),
                    height=widget.height(),
                )
            finally:
                setattr(widget, "_macos_fullscreen_promotion_pending", False)

        # Let Cocoa finish the zoom animation before starting fullscreen. The
        # former immediate conversion left both native animations alive and
        # their delayed completions alternated the window between two states.
        QTimer.singleShot(0, finish_promotion)
        return True
    return False


def strip_leading_indexes(filename: str) -> str:
    name = filename
    while True:
        new_name = LEADING_INDEX_RE.sub("", name, count=1)
        if new_name == name:
            break
        name = new_name
    return name.strip() or filename


def strip_order_prefixes(filename: str) -> str:
    name = filename
    while True:
        new_name = DATE_PREFIX_RE.sub("", name).strip()
        new_name = strip_leading_indexes(new_name)
        if new_name == name:
            break
        name = new_name
    return name.strip() or filename


def natural_text_key(text: str) -> Tuple[Tuple[int, object], ...]:
    parts: List[Tuple[int, object]] = []
    for part in NATURAL_PART_RE.split(text):
        if not part:
            continue
        if part.isdigit():
            parts.append((0, int(part)))
        else:
            parts.append((1, part.casefold()))
    return tuple(parts)


@lru_cache(maxsize=65536)
def natural_path_key(path: Path) -> Tuple[Tuple[int, object], ...]:
    return natural_text_key(path.name)


def unique_path(path: Path) -> Path:
    if not path.exists():
        return path

    parent = path.parent
    stem = path.stem
    suffix = path.suffix

    i = 1
    while True:
        candidate = parent / f"{stem} ({i}){suffix}"
        if not candidate.exists():
            return candidate
        i += 1


def is_ignored_fs_entry(path: Path) -> bool:
    name = path.name
    if name.startswith("._"):
        return True
    if name in IGNORED_FILE_NAMES:
        return True
    if path.is_dir() and name in IGNORED_FOLDER_NAMES:
        return True
    return False


def list_files(folder: Path) -> List[Path]:
    try:
        return [p for p in folder.iterdir() if p.is_file() and not is_ignored_fs_entry(p)]
    except OSError:
        return []


def list_files_recursive(
    folder: Path,
    *,
    progress_callback: Optional[Callable[[int, Path], None]] = None,
    cancel_check: Optional[Callable[[], None]] = None,
    error_callback: Optional[Callable[[OSError], None]] = None,
) -> List[Path]:
    files: List[Path] = []
    last_progress_at = 0.0
    last_progress_count = -1
    def report_walk_error(error: OSError):
        if error_callback is not None:
            error_callback(error)

    try:
        for root, dirs, names in os.walk(folder, onerror=report_walk_error, followlinks=False):
            if cancel_check is not None:
                cancel_check()
            root_path = Path(root)
            dirs[:] = [name for name in dirs if not is_ignored_fs_entry(root_path / name)]
            for name in names:
                path = root_path / name
                # os.walk already separates directories from non-directories.
                # Preserve broken file symlinks so Bad File Scan can report them
                # instead of silently skipping them.
                try:
                    mode = path.lstat().st_mode
                except OSError as exc:
                    report_walk_error(exc)
                    files.append(path)
                    continue
                if (
                    stat_module.S_ISREG(mode) or stat_module.S_ISLNK(mode)
                ) and not is_ignored_fs_entry(path):
                    files.append(path)
            now = time.monotonic()
            file_count = len(files)
            if (
                progress_callback is not None
                and file_count != last_progress_count
                and (
                    last_progress_count < 0
                    or file_count - last_progress_count >= 250
                    or now - last_progress_at >= 0.5
                )
            ):
                progress_callback(file_count, root_path)
                last_progress_at = now
                last_progress_count = file_count
    except OSError as exc:
        report_walk_error(exc)
    if progress_callback is not None and len(files) != last_progress_count:
        progress_callback(len(files), Path(folder))
    return files


def recursive_file_set_is_stable(
    folder: Path,
    original_files: Sequence[Path],
    *,
    cancel_check: Callable[[], None],
    allowed_missing_paths: Iterable[Path] = (),
) -> Tuple[bool, int]:
    """Re-enumerate after a long scan so unexpected changes cannot go unnoticed.

    Scanner dialogs may deliberately move already-reviewed results to Trash
    while remaining work continues. Those exact, app-owned removals are allowed;
    every unrelated addition/removal still invalidates the scan.
    """
    errors: List[OSError] = []
    current_files = list_files_recursive(
        folder,
        cancel_check=cancel_check,
        error_callback=errors.append,
    )
    if errors:
        return False, len(errors)
    original_set = {os.fspath(path) for path in original_files}
    current_set = {os.fspath(path) for path in current_files}
    allowed_missing = {os.fspath(path) for path in allowed_missing_paths}
    differences = original_set.symmetric_difference(current_set)
    unexpected = {
        path_text
        for path_text in differences
        if not (
            path_text in allowed_missing
            and path_text in original_set
            and path_text not in current_set
        )
    }
    return not unexpected, len(unexpected)


def list_child_folders(folder: Path) -> List[Path]:
    try:
        return [p for p in folder.iterdir() if p.is_dir() and not is_ignored_fs_entry(p)]
    except OSError:
        return []


def direct_entry_signature(folder: Path) -> Tuple[Tuple[str, str], ...]:
    """Return a cheap snapshot of the visible direct entries in a folder."""
    visible_entries: List[Tuple[str, str]] = []
    try:
        with os.scandir(folder) as entries:
            for entry in entries:
                name = entry.name
                if name.startswith("._") or name in IGNORED_FILE_NAMES:
                    continue
                try:
                    if entry.is_dir(follow_symlinks=False):
                        if name in IGNORED_FOLDER_NAMES:
                            continue
                        entry_kind = "d"
                    elif entry.is_file(follow_symlinks=False):
                        entry_kind = "f"
                    else:
                        continue
                except OSError:
                    continue
                visible_entries.append((name, entry_kind))
    except OSError:
        return ()
    return tuple(sorted(visible_entries, key=lambda value: (value[0].casefold(), value[0], value[1])))


def mac_creation_time(path: Path) -> float:
    st = path.stat()
    created = getattr(st, "st_birthtime", st.st_ctime)
    try:
        datetime.fromtimestamp(created)
    except (OverflowError, OSError, ValueError):
        created = st.st_mtime
    return created


def sortable_creation_time(path: Path) -> float:
    try:
        return mac_creation_time(path)
    except OSError:
        return 0.0


def sortable_file_size(path: Path) -> int:
    try:
        return int(path.stat().st_size)
    except OSError:
        return 0


def human_size(num_bytes: int) -> str:
    units = ["B", "KB", "MB", "GB", "TB"]
    size = float(num_bytes)
    for unit in units:
        if size < 1024 or unit == units[-1]:
            if unit == "B":
                return f"{int(size)} {unit}"
            return f"{size:.2f} {unit}"
        size /= 1024
    return f"{num_bytes} B"


def human_count(value: int) -> str:
    return f"{value:,}"


def date_text(timestamp: float) -> str:
    try:
        return datetime.fromtimestamp(timestamp).strftime("%Y-%m-%d %H:%M:%S")
    except (OverflowError, OSError, TypeError, ValueError):
        return "--"


def file_change_signature(path: Path) -> Tuple[int, int, int, int, int]:
    stat = path.stat()
    return (
        int(stat.st_size),
        int(stat.st_mtime_ns),
        int(getattr(stat, "st_ctime_ns", int(stat.st_ctime * 1_000_000_000))),
        int(stat.st_dev),
        int(stat.st_ino),
    )


def sha256_file(path: Path, chunk_size: int = 1024 * 1024) -> str:
    starting_signature = file_change_signature(path)
    h = hashlib.sha256()
    with path.open("rb") as f:
        while True:
            raise_if_scan_cancelled()
            chunk = f.read(chunk_size)
            if not chunk:
                break
            h.update(chunk)
    if file_change_signature(path) != starting_signature:
        raise OSError("file changed while its SHA-256 hash was being calculated")
    return h.hexdigest()


def hamming_hex(a: str, b: str) -> int:
    try:
        return (int(a, 16) ^ int(b, 16)).bit_count()
    except Exception:
        return 999999


def perceptual_hash_band_keys(value: str, max_distance: int) -> Tuple[Tuple[int, int, int], ...]:
    """Index a hex hash without losing any match inside the Hamming threshold."""
    try:
        text = str(value).strip().lower()
        raw = int(text, 16)
    except Exception:
        return ()
    if not text or max_distance < 0:
        return ()

    bit_count = len(text) * 4
    # More bands make the index selective. A pair within max_distance can affect
    # at most that many bands, so it must still share at least
    # ``band_count - max_distance`` exact bands.
    band_count = min(bit_count, max(16, max_distance + 1))
    keys: List[Tuple[int, int, int]] = []
    for band in range(band_count):
        start = band * bit_count // band_count
        end = (band + 1) * bit_count // band_count
        width = max(1, end - start)
        keys.append((len(text), band, (raw >> start) & ((1 << width) - 1)))
    return tuple(keys)


class PerceptualHashBandIndex:
    """Bitset-backed exact candidate index for Hamming-distance searches."""

    def __init__(self, max_distance: int):
        self.max_distance = max(0, int(max_distance))
        self.band_masks: Dict[Tuple[int, int, int], int] = defaultdict(int)
        self.records: List[Tuple[Path, int]] = []

    def add(self, value: str, record: Tuple[Path, int]):
        keys = perceptual_hash_band_keys(value, self.max_distance)
        if not keys:
            return
        record_id = len(self.records)
        self.records.append(record)
        record_bit = 1 << record_id
        for key in keys:
            self.band_masks[key] |= record_bit

    def candidates(self, value: str) -> List[Tuple[Path, int]]:
        keys = perceptual_hash_band_keys(value, self.max_distance)
        if not keys or not self.records:
            return []
        required = max(1, len(keys) - self.max_distance)
        at_least = [0] * (required + 1)
        for key in keys:
            mask = self.band_masks.get(key, 0)
            for count in range(required, 1, -1):
                at_least[count] |= at_least[count - 1] & mask
            at_least[1] |= mask

        matched = at_least[required]
        result: List[Tuple[Path, int]] = []
        while matched:
            lowest_bit = matched & -matched
            record_id = lowest_bit.bit_length() - 1
            result.append(self.records[record_id])
            matched ^= lowest_bit
        return result


def bundled_binary_path(name: str) -> Optional[str]:
    """Find helper binaries even when a GUI launch has a stripped macOS PATH."""
    candidates: List[Path] = []
    if getattr(sys, "frozen", False):
        executable_dir = Path(sys.executable).resolve().parent
        candidates.extend(
            [
                executable_dir / name,
                executable_dir.parent / "Resources" / name,
                executable_dir.parent / "Frameworks" / name,
                Path(getattr(sys, "_MEIPASS", "")) / name,
            ]
        )
    else:
        # Sandboxed IDEs such as CodeRunner can read the selected project but
        # may not be allowed to execute Homebrew binaries under /opt. Reuse the
        # signed helper copies in this project's freshly built app bundles so
        # running the original .py has the same media capabilities as the app.
        module_dir = Path(__file__).resolve().parent
        try:
            entry_dir = Path(sys.argv[0]).resolve().parent
        except Exception:
            entry_dir = module_dir
        programs_root = module_dir.parent
        candidates.extend(
            [
                entry_dir / name,
                entry_dir / "bin" / name,
                entry_dir / "dist" / "Folder Manager.app" / "Contents" / "Frameworks" / name,
                entry_dir / "dist" / "Delta Downloader.app" / "Contents" / "Frameworks" / name,
                module_dir / name,
                module_dir / "bin" / name,
                programs_root / "Folder_Manager" / "app" / "dist" / "Folder Manager.app" / "Contents" / "Frameworks" / name,
                programs_root / "Delta_Downloader" / "app" / "dist" / "Delta Downloader.app" / "Contents" / "Frameworks" / name,
            ]
        )

    # App-support copies used by Delta and Folder Manager builds.  Looking in
    # both locations is harmless and lets either standalone program reuse a
    # helper that is already present without depending on the other program.
    home = Path.home()
    candidates.extend(
        [
            home / "Library" / "Application Support" / "Folder Manager" / "ffmpeg-bin" / name,
            home / "Library" / "Application Support" / "Delta Downloader" / "ffmpeg-bin" / name,
            home / ".yt_dlp_qt_downloader" / "ffmpeg-bin" / name,
        ]
    )

    found = shutil.which(name)
    if found:
        candidates.append(Path(found))
    candidates.extend(
        [
            Path("/opt/homebrew/bin") / name,
            Path("/opt/homebrew/opt/ffmpeg/bin") / name,
            Path("/usr/local/bin") / name,
            Path("/usr/local/opt/ffmpeg/bin") / name,
            Path("/opt/local/bin") / name,
            Path("/usr/bin") / name,
        ]
    )

    # imageio-ffmpeg ships a self-contained executable and is common in Python
    # media environments.  Use it when available rather than declaring ffmpeg
    # missing just because the shell PATH is unavailable to a GUI process.
    if name == "ffmpeg":
        try:
            import imageio_ffmpeg  # type: ignore
            imageio_exe = imageio_ffmpeg.get_ffmpeg_exe()
            if imageio_exe:
                candidates.append(Path(imageio_exe))
        except Exception:
            pass

    seen = set()
    for candidate in candidates:
        try:
            candidate = Path(candidate).expanduser()
            key = str(candidate)
            if key in seen:
                continue
            seen.add(key)
            # Do not let a same-named directory or another non-file shadow a
            # valid helper later in the search order. This matters for source
            # launches because the entry directory is intentionally checked
            # before Homebrew and the built-app fallbacks.
            if candidate.is_file() and os.access(candidate, os.X_OK):
                return str(candidate)
        except Exception:
            continue
    return None


def ffmpeg_path() -> Optional[str]:
    return bundled_binary_path("ffmpeg")


def ffprobe_path() -> Optional[str]:
    return bundled_binary_path("ffprobe")


def ffmpeg_hwaccel_args() -> List[str]:
    if sys.platform == "darwin":
        return ["-hwaccel", "videotoolbox"]
    return []


def ffmpeg_exists() -> bool:
    return ffmpeg_path() is not None


def reveal_in_finder(path: Path):
    if not path.exists():
        return

    def reveal():
        if sys.platform == "darwin":
            parent = path if path.is_dir() else path.parent
            script = (
                "on run argv\n"
                "set itemPath to POSIX file (item 1 of argv)\n"
                "set parentPath to POSIX file (item 2 of argv)\n"
                "tell application \"Finder\"\n"
                "activate\n"
                "if (count of Finder windows) = 0 then\n"
                "open parentPath\n"
                "else\n"
                "set target of front Finder window to parentPath\n"
                "end if\n"
                "select itemPath\n"
                "end tell\n"
                "end run"
            )
            try:
                result = subprocess.run(
                    ["osascript", "-e", script, str(path), str(parent)],
                    text=True,
                    capture_output=True,
                    timeout=10,
                )
                if result.returncode == 0:
                    return
            except Exception:
                pass
        try:
            subprocess.Popen(
                ["open", "-R", str(path)],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
            )
        except OSError:
            pass

    threading.Thread(target=reveal, name="folder-manager-reveal", daemon=True).start()


def open_folder_in_finder(path: Path):
    if not path.exists() or not path.is_dir():
        return

    def open_folder():
        if sys.platform == "darwin":
            script = (
                "on run argv\n"
                "set folderPath to POSIX file (item 1 of argv)\n"
                "tell application \"Finder\"\n"
                "activate\n"
                "if (count of Finder windows) = 0 then\n"
                "open folderPath\n"
                "else\n"
                "set target of front Finder window to folderPath\n"
                "end if\n"
                "end tell\n"
                "end run"
            )
            try:
                result = subprocess.run(
                    ["osascript", "-e", script, str(path)],
                    text=True,
                    capture_output=True,
                    timeout=10,
                )
                if result.returncode == 0:
                    return
            except Exception:
                pass
        try:
            subprocess.Popen(
                ["open", str(path)],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
            )
        except OSError:
            pass

    threading.Thread(target=open_folder, name="folder-manager-open-folder", daemon=True).start()


def open_file_reusing_finder(path: Path):
    if not path.exists():
        return
    subprocess.Popen(["open", str(path)], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)


def ffprobe_duration(path: Path) -> Optional[float]:
    probe = ffprobe_path()
    if probe is None:
        return None
    try:
        result = scan_subprocess_run(
            [
                probe,
                "-v",
                "error",
                "-show_entries",
                "format=duration",
                "-of",
                "default=noprint_wrappers=1:nokey=1",
                str(path),
            ],
            text=True,
            capture_output=True,
            timeout=20,
        )
        if result.returncode != 0:
            return None
        return float(result.stdout.strip())
    except ScanCancelled:
        raise
    except Exception:
        return None


# ---------------------------------------------------------------------------
# Media metadata and playback diagnostics


@dataclass
class MediaMeta:
    duration: str = ""
    sample_rate: str = ""
    resolution: str = ""
    frame_rate: str = ""
    video_codec: str = ""
    audio_codec: str = ""
    bit_rate: str = ""
    duration_seconds: float = 0.0
    sample_rate_hz: int = 0
    frame_rate_fps: float = 0.0
    bit_rate_bps: int = 0
    width: int = 0
    height: int = 0


@lru_cache(maxsize=1024)
def _container_video_codec_hint(
    path_text: str,
    file_size: int,
    modified_ns: int,
) -> str:
    """Read only the container header to identify codecs Qt cannot display.

    Matroska/WebM stores its CodecID near the beginning of the file, and MP4
    sample entries normally expose the four-character codec tag there as well.
    This inexpensive check avoids starting Qt's known-broken AV1 decoder while
    the asynchronous ffprobe metadata request is still in flight.
    """
    del file_size, modified_ns  # These values intentionally invalidate the cache.
    try:
        with Path(path_text).open("rb") as handle:
            header = handle.read(1024 * 1024)
    except OSError:
        return ""
    if b"V_AV1" in header or b"av01" in header:
        return "av1"
    if b"V_VP9" in header or b"vp09" in header:
        return "vp9"
    if b"V_VP8" in header or b"vp08" in header:
        return "vp8"
    return ""


def container_video_codec_hint(path: Path) -> str:
    """Return a cheap codec hint without launching ffprobe on the GUI thread."""
    try:
        stat = path.stat()
    except OSError:
        return ""
    return _container_video_codec_hint(
        str(path),
        int(stat.st_size),
        int(stat.st_mtime_ns),
    )


def preview_requires_compatibility_proxy(
    path: Path,
    meta: Optional[MediaMeta] = None,
) -> bool:
    """Identify codecs that require the buffered compatibility playback path."""
    # This is a codec-routing decision, not a helper-availability decision.
    # In particular, AV1/VP8/VP9 do not become safe for direct Qt playback
    # merely because FFmpeg could not be found. Keeping those facts separate
    # prevents the exact failure mode where Qt reports Playing/Buffered while
    # producing zero video frames and the UI stays black. Apply the policy by
    # codec rather than container so WebM and MKV behave identically.
    if sys.platform != "darwin" or not is_video_path(path):
        return False
    codec = str(getattr(meta, "video_codec", "") or "").strip().casefold()
    normalized_codec = codec.replace("-", "").replace("_", "")
    if normalized_codec in {"av1", "av01", "vp8", "vp08", "vp9", "vp09"}:
        return True
    if codec:
        return False
    return container_video_codec_hint(path) in {"av1", "vp8", "vp9"}


def preview_direct_watchdog_delay_ms(
    path: Path,
    meta: Optional[MediaMeta] = None,
    *,
    autoplay: bool = True,
) -> int:
    """Return the no-frame grace period for direct preview playback.

    Known-problem codecs get a short grace period regardless of whether their
    container is WebM or Matroska.  This keeps first use responsive while still
    allowing Qt's decoder to avoid an unnecessary full-file proxy conversion.
    """
    if preview_requires_compatibility_proxy(path, meta) or path.suffix.lower() == ".webm":
        return 850
    return 5000 if autoplay else 650


def preview_source_kind(owner) -> str:
    """Describe the source currently handed to Qt without exposing its path."""
    if bool(getattr(owner, "playing_compatibility_proxy", False)):
        candidate = getattr(owner, "bound_compatibility_proxy_path", None)
        if candidate is None:
            player = getattr(owner, "media_player", None)
            try:
                source = player.source() if player is not None else None
                local_file = str(source.toLocalFile() or "") if source is not None else ""
                candidate = Path(local_file) if local_file else None
            except (AttributeError, RuntimeError, TypeError, ValueError):
                candidate = None
        if candidate is not None and Path(candidate).name.startswith("."):
            return "growing compatibility proxy"
        return "validated compatibility proxy"
    current = getattr(owner, "current_path", None)
    proxy_source = getattr(owner, "playable_proxy_source", None)
    if current is not None and proxy_source == current:
        workers = getattr(owner, "playable_proxy_workers", ())
        if preview_proxy_running(workers, Path(current)):
            return "compatibility proxy preparing"
    recovery = getattr(owner, "playback_recovery_source", None)
    if current is not None and recovery == current:
        return "original media"
    if bool(getattr(owner, "poster_only", False)):
        return "static poster"
    if current is not None:
        try:
            if Path(current).suffix.lower() in AUDIO_EXTS:
                return "original audio"
            if is_video_path(Path(current)):
                return "original media"
        except (OSError, TypeError, ValueError):
            pass
    return "not assigned"


def media_preview_descriptor(
    path: Path,
    meta: Optional[MediaMeta] = None,
    info=None,
) -> Dict[str, object]:
    """Return safe type/codec fields shared by both preview surfaces."""
    meta = meta or MediaMeta()
    info = info if info is not None else file_info(path)
    header_codec = (
        container_video_codec_hint(path)
        if is_video_path(path) and not str(meta.video_codec or "").strip()
        else ""
    )
    return {
        "container": path.suffix.lower().lstrip(".") or "none",
        "kind": kind_for_path(path),
        "mime": str(getattr(info, "mime", "") or mimetypes.guess_type(path.name)[0] or "unknown"),
        "video_codec": str(meta.video_codec or header_codec or "unknown"),
        "audio_codec": str(meta.audio_codec or "unknown"),
        "resolution": str(meta.resolution or "unknown"),
        "duration_ms": max(0, round(float(meta.duration_seconds or 0.0) * 1000.0)),
        "source_bytes": max(0, int(getattr(info, "size", 0) or 0)),
    }


def qmedia_player_snapshot(player) -> Dict[str, object]:
    """Read QMediaPlayer state defensively while it is changing sources."""
    snapshot: Dict[str, object] = {}
    if player is None:
        return snapshot
    for key, method_name, default in (
        ("has_video", "hasVideo", False),
        ("has_audio", "hasAudio", False),
        ("player_seekable", "isSeekable", False),
        ("position_ms", "position", 0),
        ("duration_ms", "duration", 0),
    ):
        try:
            snapshot[key] = getattr(player, method_name)()
        except (AttributeError, RuntimeError, TypeError):
            snapshot[key] = default
    try:
        snapshot["buffer_percent"] = round(float(player.bufferProgress()) * 100.0, 1)
    except (AttributeError, RuntimeError, TypeError, ValueError):
        snapshot["buffer_percent"] = 0.0
    for key, method_name in (
        ("player_media_status", "mediaStatus"),
        ("player_playback_state", "playbackState"),
        ("player_error", "error"),
    ):
        try:
            snapshot[key] = qt_enum_name(getattr(player, method_name)())
        except (AttributeError, RuntimeError, TypeError):
            snapshot[key] = "unavailable"
    try:
        error_text = str(player.errorString() or "").strip()
    except (AttributeError, RuntimeError, TypeError):
        error_text = ""
    if error_text:
        snapshot["player_error_text"] = _clean_process_diagnostic(error_text, limit=500)
    try:
        tracks = list(player.audioTracks())
    except (AttributeError, RuntimeError, TypeError):
        tracks = []
    try:
        active_track = int(player.activeAudioTrack())
    except (AttributeError, RuntimeError, TypeError, ValueError):
        active_track = -1
    snapshot["audio_track_count"] = len(tracks)
    snapshot["active_audio_track"] = active_track
    try:
        output = player.audioOutput()
    except (AttributeError, RuntimeError, TypeError):
        output = None
    snapshot.update(audio_output_snapshot(output))
    return snapshot


def _audio_device_identifier(device) -> str:
    """Return a stable, privacy-safe route identifier (never a device name)."""
    if device is None:
        return "none"
    try:
        if device.isNull():
            return "none"
        raw = bytes(device.id())
    except (AttributeError, RuntimeError, TypeError, ValueError):
        return "unknown"
    return hashlib.sha256(raw).hexdigest()[:12] if raw else "unknown"


def audio_output_snapshot(audio_output) -> Dict[str, object]:
    snapshot: Dict[str, object] = {
        "audio_output_attached": audio_output is not None,
        "audio_output_muted": False,
        "audio_output_volume_percent": 0,
        "audio_device_id": "none",
        "audio_device_is_default": False,
    }
    if audio_output is None:
        return snapshot
    try:
        snapshot["audio_output_muted"] = bool(audio_output.isMuted())
        snapshot["audio_output_volume_percent"] = round(float(audio_output.volume()) * 100.0)
        device = audio_output.device()
        snapshot["audio_device_id"] = _audio_device_identifier(device)
        if QMediaDevices is not None:
            default_device = QMediaDevices.defaultAudioOutput()
            snapshot["audio_device_is_default"] = bool(
                not device.isNull() and not default_device.isNull() and device == default_device
            )
    except (AttributeError, RuntimeError, TypeError, ValueError):
        snapshot["audio_output_state"] = "unavailable"
    return snapshot


def audio_buffer_snapshot(monitor) -> Dict[str, object]:
    if monitor is None:
        return {
            "audio_buffers_decoded": 0,
            "audio_frames_decoded": 0,
            "audio_bytes_decoded": 0,
            "audio_first_buffer_ms": -1,
            "audio_last_buffer_age_ms": -1,
            "audio_sample_rate": 0,
            "audio_channels": 0,
            "audio_sample_format": "unknown",
        }
    try:
        now = time.monotonic()
        first_ms = (
            round((float(monitor.first_buffer_at) - float(monitor.source_started_at)) * 1000)
            if monitor.first_buffer_at and monitor.source_started_at
            else -1
        )
        age_ms = round((now - float(monitor.last_buffer_at)) * 1000) if monitor.last_buffer_at else -1
        return {
            "audio_buffers_decoded": int(monitor.buffer_count),
            "audio_frames_decoded": int(monitor.frame_count),
            "audio_bytes_decoded": int(monitor.byte_count),
            "audio_first_buffer_ms": first_ms,
            "audio_last_buffer_age_ms": age_ms,
            "audio_sample_rate": int(monitor.sample_rate),
            "audio_channels": int(monitor.channel_count),
            "audio_sample_format": str(monitor.sample_format or "unknown"),
            "audio_non_silent_observed": bool(monitor.non_silent_observed),
        }
    except (AttributeError, RuntimeError, TypeError, ValueError):
        return {"audio_monitor_state": "unavailable"}


def preview_surface_snapshot(owner) -> Dict[str, object]:
    """Capture the full audio/video/control ownership contract for diagnostics."""
    if owner is None:
        return {}
    snapshot: Dict[str, object] = {
        "surface_role": preview_owner_role(owner),
        "external_owner": bool(getattr(owner, "external_playback_owner", None)),
        "media_playback_requested": bool(getattr(owner, "media_playback_requested", False)),
        "poster_only": bool(getattr(owner, "poster_only", False)),
    }
    try:
        snapshot["surface_visible"] = bool(owner.isVisible())
    except (AttributeError, RuntimeError):
        snapshot["surface_visible"] = False
    player = getattr(owner, "media_player", None)
    snapshot.update(qmedia_player_snapshot(player))
    snapshot.update(video_frame_snapshot(getattr(owner, "video_widget", None)))
    snapshot.update(audio_buffer_snapshot(getattr(owner, "audio_monitor", None)))
    try:
        stack = getattr(owner, "preview_stack", None) or getattr(owner, "stack", None)
        current_page = stack.currentWidget() if stack is not None else None
        snapshot["preview_page"] = (
            _interaction_short_label(current_page.objectName()) if current_page is not None else "none"
        )
    except (AttributeError, RuntimeError):
        snapshot["preview_page"] = "unavailable"
    for name in ("play_button", "scrub_slider", "mute_button", "paused_overlay"):
        widget = getattr(owner, name, None)
        try:
            snapshot[f"{name}_visible"] = bool(widget is not None and widget.isVisible())
            snapshot[f"{name}_enabled"] = bool(widget is not None and widget.isEnabled())
        except RuntimeError:
            snapshot[f"{name}_visible"] = False
            snapshot[f"{name}_enabled"] = False
    slider = getattr(owner, "scrub_slider", None)
    try:
        snapshot.update(
            {
                "slider_value_ms": int(slider.value()),
                "slider_minimum_ms": int(slider.minimum()),
                "slider_maximum_ms": int(slider.maximum()),
            }
        )
    except (AttributeError, RuntimeError, TypeError, ValueError):
        snapshot.update(
            {
                "slider_value_ms": 0,
                "slider_minimum_ms": 0,
                "slider_maximum_ms": 0,
            }
        )
    seeker = getattr(owner, "scrub_seeker", None)
    snapshot.update(
        {
            "logical_duration_ms": max(0, int(getattr(owner, "media_duration_ms", 0) or 0)),
            "metadata_duration_ms": max(0, int(getattr(owner, "metadata_duration_ms", 0) or 0)),
            "pending_seek_ms": getattr(owner, "pending_media_seek_ms", None),
            "seek_ack_target_ms": getattr(seeker, "committed_position", None),
            "seek_revision": max(0, int(getattr(seeker, "commit_revision", 0) or 0)),
            "seek_reason": str(getattr(seeker, "committed_reason", "") or "none"),
            "scrubbing": bool(getattr(owner, "scrubbing_video", False)),
            "proxy_rebind_pending": bool(getattr(owner, "_proxy_rebind_pending", False)),
            "proxy_rebind_generation": max(
                0,
                int(getattr(owner, "_proxy_rebind_generation", 0) or 0),
            ),
            "provisional_proxy": bool(getattr(owner, "awaiting_final_proxy", False)),
            "provisional_resume_position_ms": max(
                0,
                int(getattr(owner, "_provisional_resume_position_ms", 0) or 0),
            ),
        }
    )
    large_owner = visible_large_preview_owner(excluding=owner)
    snapshot["large_preview_visible"] = large_owner is not None
    try:
        embedded_playing = (
            preview_owner_role(owner) == "embedded"
            and player is not None
            and QMediaPlayer is not None
            and player.playbackState() == QMediaPlayer.PlaybackState.PlayingState
        )
    except (AttributeError, RuntimeError):
        embedded_playing = False
    snapshot["ownership_ok"] = not (embedded_playing and large_owner is not None)
    return snapshot


class PreviewAudioMonitor(QObject):
    """Observe decoded audio without changing the audio sent to the speakers."""

    def __init__(self, owner, player, surface: str):
        super().__init__(owner)
        self.owner_ref = weakref.ref(owner)
        self.player_ref = weakref.ref(player)
        self.surface = str(surface or "unknown")
        self.output = None
        self.health_timer = QTimer(self)
        self.health_timer.setSingleShot(True)
        self.health_timer.timeout.connect(self.report_health)
        self.reset()
        if QAudioBufferOutput is not None:
            try:
                self.output = QAudioBufferOutput(self)
                self.output.audioBufferReceived.connect(self.on_audio_buffer)
                player.setAudioBufferOutput(self.output)
            except (AttributeError, RuntimeError, TypeError) as exc:
                self.output = None
                debug_log(
                    "media-preview",
                    "decoded audio monitor unavailable",
                    force=True,
                    surface=self.surface,
                    error=type(exc).__name__,
                )
        try:
            player.playbackStateChanged.connect(self.on_playback_state_changed)
        except (AttributeError, RuntimeError):
            pass

    def reset(self):
        self.health_timer.stop() if hasattr(self, "health_timer") else None
        owner = self.owner_ref() if hasattr(self, "owner_ref") else None
        self.source_item_id = preview_item_id(getattr(owner, "current_path", None))
        self.source_started_at = time.monotonic()
        self.first_buffer_at = 0.0
        self.last_buffer_at = 0.0
        self.buffer_count = 0
        self.frame_count = 0
        self.byte_count = 0
        self.sample_rate = 0
        self.channel_count = 0
        self.sample_format = "unknown"
        self.non_silent_observed = False
        self._first_buffer_logged = False
        self._health_reports = 0

    def arm_health_check(self, delay_ms: int = 2600):
        if self.output is not None:
            self.health_timer.start(max(250, int(delay_ms)))

    def on_playback_state_changed(self, state):
        if QMediaPlayer is not None and state == QMediaPlayer.PlaybackState.PlayingState:
            self.arm_health_check()

    def on_audio_buffer(self, buffer):
        try:
            owner = self.owner_ref()
            player = self.player_ref()
            if owner is None or preview_item_id(getattr(owner, "current_path", None)) != self.source_item_id:
                # QMediaPlayer can deliver a queued buffer from the old source
                # after the selected row changed. Never attribute that audio to
                # the new preview session.
                return
            if player is None:
                return
            if (
                QMediaPlayer is not None
                and player.playbackState() != QMediaPlayer.PlaybackState.PlayingState
            ):
                # The same item can transition from a playing source to a
                # poster-only mirror. Item identity alone cannot distinguish a
                # queued buffer from that detached session.
                return
            try:
                source = player.source()
                if source is None or source.isEmpty():
                    return
            except (AttributeError, RuntimeError):
                return
            if not buffer.isValid() or int(buffer.frameCount()) <= 0:
                return
            now = time.monotonic()
            if not self.first_buffer_at:
                self.first_buffer_at = now
            self.last_buffer_at = now
            self.buffer_count += 1
            self.frame_count += int(buffer.frameCount())
            self.byte_count += int(buffer.byteCount())
            audio_format = buffer.format()
            self.sample_rate = int(audio_format.sampleRate())
            self.channel_count = int(audio_format.channelCount())
            self.sample_format = qt_enum_name(audio_format.sampleFormat())
            # A non-empty decoded buffer proves liveness.  Avoid copying or
            # logging user audio samples; diagnostics need state, not content.
            self.non_silent_observed = self.non_silent_observed or int(buffer.byteCount()) > 0
            if self._first_buffer_logged:
                return
            self._first_buffer_logged = True
            preview_trace(
                self.surface,
                "first decoded audio buffer",
                getattr(owner, "current_path", None),
                force=True,
                source_kind=preview_source_kind(owner) if owner is not None else "unknown",
                decision="audio decoder produced data",
                **audio_buffer_snapshot(self),
                **qmedia_player_snapshot(self.player_ref()),
            )
        except (AttributeError, RuntimeError, TypeError, ValueError):
            return

    def report_health(self):
        owner = self.owner_ref()
        player = self.player_ref()
        if owner is None or player is None:
            return
        if preview_item_id(getattr(owner, "current_path", None)) != self.source_item_id:
            return
        try:
            if (
                QMediaPlayer is not None
                and player.playbackState() != QMediaPlayer.PlaybackState.PlayingState
            ):
                # A timer armed by an earlier PlayingState may fire after the
                # user paused, changed rows, or entered proxy preparation.
                # Reporting old counters here made stopped previews look as if
                # their audio was still flowing.
                return
        except (AttributeError, RuntimeError):
            return
        snapshot = qmedia_player_snapshot(player)
        snapshot.update(audio_buffer_snapshot(self))
        decoded = self.buffer_count > 0
        has_audio = bool(snapshot.get("has_audio")) or int(snapshot.get("audio_track_count", 0)) > 0
        muted = bool(snapshot.get("audio_output_muted"))
        if has_audio and not decoded:
            try:
                if int(snapshot.get("audio_track_count", 0)) > 0 and int(snapshot.get("active_audio_track", -1)) < 0:
                    player.setActiveAudioTrack(0)
                    snapshot["audio_track_recovery"] = "selected track 0"
            except (AttributeError, RuntimeError, TypeError, ValueError):
                snapshot["audio_track_recovery"] = "selection failed"
        combined = dict(snapshot)
        combined.update(preview_surface_snapshot(owner))
        preview_trace(
            self.surface,
            "audio playback health checkpoint",
            getattr(owner, "current_path", None),
            force=bool(has_audio and not decoded and not muted),
            source_kind=preview_source_kind(owner),
            decision=(
                "decoded audio is flowing"
                if decoded
                else ("media has audio but no decoded buffer arrived" if has_audio else "source reports no audio track")
            ),
            **combined,
        )


def install_preview_audio_diagnostics(owner, player, audio_output, surface: str):
    """Attach route/track/decoded-buffer diagnostics to one preview surface."""
    if player is None:
        return None
    monitor = PreviewAudioMonitor(owner, player, surface)
    setattr(owner, "audio_monitor", monitor)
    owner_ref = weakref.ref(owner)

    def route_changed(*_args):
        current_owner = owner_ref()
        if current_owner is None:
            return
        preview_trace(
            surface,
            "audio output state changed",
            getattr(current_owner, "current_path", None),
            source_kind=preview_source_kind(current_owner),
            **audio_output_snapshot(audio_output),
            **audio_buffer_snapshot(monitor),
        )

    if audio_output is not None:
        for signal_name in ("mutedChanged", "volumeChanged", "deviceChanged"):
            try:
                getattr(audio_output, signal_name).connect(route_changed)
            except (AttributeError, RuntimeError):
                pass
    try:
        player.activeTracksChanged.connect(route_changed)
    except (AttributeError, RuntimeError):
        pass
    return monitor


def reset_preview_audio_monitor(owner):
    monitor = getattr(owner, "audio_monitor", None)
    if monitor is not None:
        monitor.reset()


def ensure_active_preview_audio_track(owner, surface: str) -> None:
    player = getattr(owner, "media_player", None)
    if player is None:
        return
    snapshot = qmedia_player_snapshot(player)
    if int(snapshot.get("audio_track_count", 0)) <= 0 or int(snapshot.get("active_audio_track", -1)) >= 0:
        return
    try:
        player.setActiveAudioTrack(0)
        preview_trace(
            surface,
            "audio track activated",
            getattr(owner, "current_path", None),
            force=True,
            source_kind=preview_source_kind(owner),
            decision="Qt exposed audio tracks but selected none; activate track 0",
            **qmedia_player_snapshot(player),
        )
    except (AttributeError, RuntimeError, TypeError, ValueError) as exc:
        preview_trace(
            surface,
            "audio track activation failed",
            getattr(owner, "current_path", None),
            force=True,
            error=type(exc).__name__,
            **snapshot,
        )


def video_frame_snapshot(widget) -> Dict[str, object]:
    if widget is None:
        return {}
    getter = getattr(widget, "frame_diagnostics", None)
    if not callable(getter):
        return {}
    try:
        return dict(getter())
    except (AttributeError, RuntimeError, TypeError, ValueError):
        return {}


SCAN_MEDIA_META_CACHE: Dict[Tuple[str, int, int], MediaMeta] = {}
SCAN_MEDIA_META_INFLIGHT: Dict[Tuple[str, int, int], concurrent.futures.Future] = {}
SCAN_MEDIA_META_LOCK = threading.Lock()
SCAN_MEDIA_META_CACHE_LIMIT = 12000


def format_duration(seconds: Optional[float]) -> str:
    if seconds is None or seconds < 0:
        return ""
    total = int(round(seconds))
    hours, remainder = divmod(total, 3600)
    minutes, secs = divmod(remainder, 60)
    if hours:
        return f"{hours}:{minutes:02d}:{secs:02d}"
    return f"{minutes}:{secs:02d}"


def format_ms(milliseconds: int) -> str:
    return format_duration(max(0, int(milliseconds)) / 1000.0) or "0:00"


def format_eta(seconds: float) -> str:
    seconds = max(0, int(round(seconds)))
    if seconds < 60:
        return f"{seconds}s"
    minutes, secs = divmod(seconds, 60)
    if minutes < 60:
        return f"{minutes}m {secs:02d}s"
    hours, minutes = divmod(minutes, 60)
    return f"{hours}h {minutes:02d}m"


def scanner_work_weight(path: Path) -> float:
    """Estimate relative scanner work without blocking on media inspection."""
    try:
        size_mb = max(0.0, path.stat().st_size / (1024.0 * 1024.0))
    except OSError:
        size_mb = 0.0
    suffix = path.suffix.lower()
    if suffix in VIDEO_EXTS:
        return max(4.0, 4.0 + min(4096.0, size_mb) / 24.0)
    if suffix in AUDIO_EXTS:
        return max(2.0, 2.0 + min(2048.0, size_mb) / 48.0)
    if suffix in IMAGE_EXTS:
        return max(0.5, 0.5 + min(256.0, size_mb) / 32.0)
    return max(0.25, 0.25 + min(512.0, size_mb) / 128.0)


class ScannerProgressEstimate:
    """Monotonic weighted progress and smoothed ETA for heterogeneous files."""

    def __init__(self, paths: Sequence[Path], started_at: Optional[float] = None):
        self.weights = {str(Path(path)): scanner_work_weight(Path(path)) for path in paths}
        self.total_work = max(0.001, sum(self.weights.values()))
        self.completed_work = 0.0
        self.completed_count = 0
        self.started_at = time.monotonic() if started_at is None else float(started_at)
        self.last_sample_at = self.started_at
        self.last_sample_work = 0.0
        self.ewma_rate = 0.0

    def complete(self, path: Path):
        self.completed_work = min(
            self.total_work,
            self.completed_work + self.weights.get(str(Path(path)), 1.0),
        )
        self.completed_count += 1
        now = time.monotonic()
        delta_time = max(0.001, now - self.last_sample_at)
        delta_work = max(0.0, self.completed_work - self.last_sample_work)
        if delta_work > 0.0:
            rate = delta_work / delta_time
            self.ewma_rate = rate if self.ewma_rate <= 0.0 else (0.3 * rate + 0.7 * self.ewma_rate)
            self.last_sample_at = now
            self.last_sample_work = self.completed_work

    def percent(self) -> int:
        return max(0, min(100, int(round(100.0 * self.completed_work / self.total_work))))

    def eta_text(self) -> str:
        elapsed = max(0.0, time.monotonic() - self.started_at)
        meaningful = self.completed_count >= 2 and elapsed >= 1.0 and self.ewma_rate > 0.0
        if not meaningful:
            return "Estimating…"
        remaining = max(0.0, self.total_work - self.completed_work)
        return f"ETA {format_eta(remaining / self.ewma_rate)}"

    def text(self, label: str, total_count: int, detail: str = "") -> str:
        text = (
            f"{label} {human_count(self.completed_count)}/{human_count(total_count)}"
            f"  |  {self.eta_text()}"
        )
        if detail:
            text = f"{text}: {detail}"
        return text


def progress_text_with_eta(label: str, index: int, total: int, started_at: float, detail: str = "") -> str:
    """Compatibility helper for uniform-work phases."""
    total = max(1, total)
    elapsed = max(0.01, time.time() - started_at)
    if index < 2 or elapsed < 1.0:
        eta = "Estimating…"
    else:
        remaining = (elapsed / max(1, index)) * max(0, total - index)
        eta = f"ETA {format_eta(remaining)}"
    text = f"{label} {human_count(index)}/{human_count(total)}  |  {eta}"
    if detail:
        text = f"{text}: {detail}"
    return text


def set_elided_label_text(label: QLabel, text: str, minimum_width: int = 260):
    label.setToolTip(text)
    width = max(minimum_width, label.width() - 8)
    label.setText(label.fontMetrics().elidedText(text, Qt.ElideMiddle, width))


@lru_cache(maxsize=65536)
def _normalized_folder_path(raw_path: str) -> str:
    try:
        return str(Path(raw_path).resolve())
    except OSError:
        return str(Path(raw_path).absolute())


def normalized_folder_path(path: Path) -> str:
    # Duplicate scans compare the same paths thousands of times. Resolving each
    # one repeatedly performs avoidable filesystem work on the GUI thread.
    return _normalized_folder_path(str(path))


def finder_window_paths(run_process: Optional[Callable] = None) -> List[str]:
    if sys.platform != "darwin":
        return []

    script = (
        "tell application \"Finder\"\n"
        "set output to \"\"\n"
        "repeat with finderWindow in Finder windows\n"
        "try\n"
        "set output to output & POSIX path of (target of finderWindow as alias) & linefeed\n"
        "end try\n"
        "end repeat\n"
        "return output\n"
        "end tell"
    )
    process_runner = run_process or subprocess.run
    try:
        result = process_runner(
            ["osascript", "-e", script],
            text=True,
            capture_output=True,
            timeout=8,
        )
        if result.returncode != 0:
            return []
        return [normalized_folder_path(Path(line.strip())) for line in result.stdout.splitlines() if line.strip()]
    except Exception:
        return []


def quality_score_for_path(path: Path, meta: MediaMeta) -> Tuple[float, float, float, float, float]:
    try:
        size = float(path.stat().st_size)
    except OSError:
        size = 0.0

    pixels = float(max(0, meta.width) * max(0, meta.height))
    duration = max(0.0, meta.duration_seconds)
    bitrate = (size * 8.0 / duration) if duration > 0 else 0.0
    sample_rate = float(max(0, meta.sample_rate_hz))
    kind = kind_for_path(path)

    if kind == "Video":
        return (pixels, sample_rate, size, bitrate, duration)
    if kind == "Audio":
        return (sample_rate, bitrate, size, duration, 0.0)
    if kind == "Image":
        return (pixels, size, 0.0, 0.0, 0.0)
    return (size, pixels, sample_rate, bitrate, duration)


def quality_summary_for_item(item: "DupItem") -> str:
    factors = []
    if item.resolution:
        factors.append(item.resolution)
    if item.duration:
        factors.append(item.duration)
    if item.sample_rate:
        factors.append(item.sample_rate)
    try:
        size = item.file.stat().st_size
        if item.duration_seconds > 0 and size > 0:
            bitrate_mbps = (size * 8.0 / item.duration_seconds) / 1_000_000
            factors.append(f"~{bitrate_mbps:.2f} Mbps")
        if size:
            factors.append(human_size(size))
    except OSError:
        pass
    return " | ".join(factors)


def float_or_none(value) -> Optional[float]:
    try:
        if value is None or value == "N/A":
            return None
        return float(value)
    except (TypeError, ValueError):
        return None


def frame_rate_value(value) -> float:
    text = str(value or "").strip()
    if not text or text == "N/A":
        return 0.0
    try:
        if "/" in text:
            numerator, denominator = text.split("/", 1)
            denominator_value = float(denominator)
            return float(numerator) / denominator_value if denominator_value else 0.0
        return float(text)
    except (TypeError, ValueError, ZeroDivisionError):
        return 0.0


def format_bitrate(bits_per_second: int) -> str:
    value = max(0, int(bits_per_second or 0))
    if value >= 1_000_000:
        return f"{value / 1_000_000:.2f} Mbps"
    if value >= 1_000:
        return f"{value / 1_000:.0f} Kbps"
    return f"{value} bps" if value else ""


def media_metadata(
    path: Path,
    run_process: Optional[Callable] = None,
    include_spotlight: bool = True,
) -> MediaMeta:
    meta = MediaMeta()
    process_runner = run_process or subprocess.run

    if path.suffix.lower() in IMAGE_EXTS:
        try:
            from PIL import Image

            with Image.open(path) as img:
                width, height = img.size
                meta.width = int(width)
                meta.height = int(height)
                meta.resolution = f"{width}x{height}"
        except Exception:
            pass

    probe = ffprobe_path()
    if probe is None:
        if include_spotlight:
            fill_spotlight_media_metadata(path, meta, run_process=process_runner)
        return meta

    try:
        result = process_runner(
            [
                probe,
                "-v",
                "error",
                "-print_format",
                "json",
                "-show_entries",
                "format=duration,bit_rate:stream=codec_type,codec_name,width,height,sample_rate,duration,avg_frame_rate,r_frame_rate,bit_rate",
                str(path),
            ],
            text=True,
            capture_output=True,
            timeout=20,
        )
        if result.returncode != 0 or not result.stdout:
            if include_spotlight:
                fill_spotlight_media_metadata(path, meta, run_process=process_runner)
            return meta

        payload = json.loads(result.stdout)
        streams = payload.get("streams", []) or []
        format_info = payload.get("format") or {}
        duration = float_or_none(format_info.get("duration"))
        format_bit_rate = int(float_or_none(format_info.get("bit_rate")) or 0)

        for stream in streams:
            duration = duration if duration is not None else float_or_none(stream.get("duration"))
            if stream.get("codec_type") == "video" and not meta.resolution:
                meta.video_codec = str(stream.get("codec_name") or "")
                width = stream.get("width")
                height = stream.get("height")
                if width and height:
                    meta.width = int(width)
                    meta.height = int(height)
                    meta.resolution = f"{width}x{height}"
                meta.frame_rate_fps = frame_rate_value(stream.get("avg_frame_rate") or stream.get("r_frame_rate"))
                if meta.frame_rate_fps > 0:
                    rounded_fps = round(meta.frame_rate_fps)
                    meta.frame_rate = (
                        f"{rounded_fps} fps"
                        if abs(meta.frame_rate_fps - rounded_fps) < 0.02
                        else f"{meta.frame_rate_fps:.2f} fps"
                    )
                meta.bit_rate_bps = int(float_or_none(stream.get("bit_rate")) or 0)
            elif stream.get("codec_type") == "audio" and not meta.sample_rate:
                meta.audio_codec = str(stream.get("codec_name") or "")
                sample_rate = stream.get("sample_rate")
                if sample_rate and sample_rate != "N/A":
                    try:
                        meta.sample_rate_hz = int(sample_rate)
                        meta.sample_rate = f"{meta.sample_rate_hz:,} Hz"
                    except (TypeError, ValueError):
                        meta.sample_rate = str(sample_rate)

        meta.duration_seconds = float(duration or 0.0)
        meta.duration = format_duration(duration)
        meta.bit_rate_bps = format_bit_rate or meta.bit_rate_bps
        meta.bit_rate = format_bitrate(meta.bit_rate_bps)
        if include_spotlight:
            fill_spotlight_media_metadata(path, meta, run_process=process_runner)
        return meta
    except (PreviewWorkerCancelled, ScanCancelled):
        raise
    except Exception:
        if include_spotlight:
            fill_spotlight_media_metadata(path, meta, run_process=process_runner)
        return meta


def fill_spotlight_media_metadata(path: Path, meta: MediaMeta, run_process: Optional[Callable] = None):
    if sys.platform != "darwin" or not path.exists():
        return
    process_runner = run_process or subprocess.run

    names = [
        "kMDItemDurationSeconds",
        "kMDItemPixelWidth",
        "kMDItemPixelHeight",
        "kMDItemAudioSampleRate",
    ]
    try:
        result = process_runner(
            ["mdls", "-raw", *[arg for name in names for arg in ("-name", name)], str(path)],
            text=True,
            capture_output=True,
            timeout=8,
        )
        if result.returncode != 0:
            return
    except (PreviewWorkerCancelled, ScanCancelled):
        raise
    except Exception:
        return

    values = [line.strip() for line in result.stdout.splitlines()]
    data = dict(zip(names, values))

    if not meta.duration:
        duration = float_or_none(data.get("kMDItemDurationSeconds"))
        if duration:
            meta.duration_seconds = float(duration)
            meta.duration = format_duration(duration)

    if not meta.resolution:
        width = float_or_none(data.get("kMDItemPixelWidth"))
        height = float_or_none(data.get("kMDItemPixelHeight"))
        if width and height:
            meta.width = int(width)
            meta.height = int(height)
            meta.resolution = f"{meta.width}x{meta.height}"

    if not meta.sample_rate:
        sample_rate = float_or_none(data.get("kMDItemAudioSampleRate"))
        if sample_rate:
            meta.sample_rate_hz = int(sample_rate)
            meta.sample_rate = f"{meta.sample_rate_hz:,} Hz"


def scanner_media_metadata(path: Path) -> MediaMeta:
    """Share one metadata probe between duplicate and bad-file scanners."""
    try:
        stat = path.stat()
        cache_key = (str(path), int(stat.st_size), int(stat.st_mtime_ns))
    except OSError:
        return media_metadata(
            path,
            run_process=scan_subprocess_run,
            include_spotlight=False,
        )

    with SCAN_MEDIA_META_LOCK:
        cached = SCAN_MEDIA_META_CACHE.get(cache_key)
        if cached is not None:
            return cached
        pending = SCAN_MEDIA_META_INFLIGHT.get(cache_key)
        owns_work = pending is None
        if owns_work:
            pending = concurrent.futures.Future()
            SCAN_MEDIA_META_INFLIGHT[cache_key] = pending

    if not owns_work:
        try:
            return wait_for_scan_future(pending, timeout=60)
        except ScanCancelled:
            raise
        except Exception:
            return MediaMeta()

    try:
        meta = media_metadata(
            path,
            run_process=scan_subprocess_run,
            include_spotlight=False,
        )
    except ScanCancelled:
        with SCAN_MEDIA_META_LOCK:
            SCAN_MEDIA_META_INFLIGHT.pop(cache_key, None)
        if pending is not None and not pending.done():
            pending.set_exception(ScanCancelled())
        raise
    except Exception:
        meta = MediaMeta()

    with SCAN_MEDIA_META_LOCK:
        if len(SCAN_MEDIA_META_CACHE) >= SCAN_MEDIA_META_CACHE_LIMIT:
            remove_count = max(1, SCAN_MEDIA_META_CACHE_LIMIT // 8)
            for old_key in list(SCAN_MEDIA_META_CACHE)[:remove_count]:
                SCAN_MEDIA_META_CACHE.pop(old_key, None)
        SCAN_MEDIA_META_CACHE[cache_key] = meta
        SCAN_MEDIA_META_INFLIGHT.pop(cache_key, None)
    if pending is not None and not pending.done():
        pending.set_result(meta)
    return meta


def user_trash_folder() -> Path:
    if sys.platform == "darwin":
        trash = Path.home() / ".Trash"
    else:
        trash = Path.home() / ".local" / "share" / "Trash" / "files"
    trash.mkdir(parents=True, exist_ok=True)
    return trash


def trash_folder_for_path(path: Path) -> Path:
    if sys.platform != "darwin":
        return user_trash_folder()
    try:
        # Choose the Trash on the volume that contains the directory entry.
        # Resolving a symlink here can incorrectly select the target's volume
        # even though the symlink itself lives somewhere else.
        resolved = path.expanduser().absolute()
    except OSError:
        resolved = path.absolute()
    parts = resolved.parts
    if len(parts) >= 3 and parts[1] == "Volumes":
        volume_trash = Path(parts[0]) / parts[1] / parts[2] / ".Trashes" / str(os.getuid())
        try:
            volume_trash.mkdir(parents=True, exist_ok=True)
            if os.access(volume_trash, os.W_OK):
                return volume_trash
        except OSError:
            pass
    return user_trash_folder()


def finder_move_to_trash_recorded(path: Path) -> Optional["TrashMove"]:
    if sys.platform != "darwin" or not path.exists():
        return None

    script = (
        "on run argv\n"
        "set itemPath to POSIX file (item 1 of argv)\n"
        "tell application \"Finder\"\n"
        "set trashedItem to delete itemPath\n"
        "return POSIX path of (trashedItem as alias)\n"
        "end tell\n"
        "end run"
    )
    try:
        result = subprocess.run(
            ["osascript", "-e", script, str(path)],
            text=True,
            capture_output=True,
            timeout=15,
        )
        if result.returncode != 0:
            return None
        trash_text = result.stdout.strip()
        if not trash_text:
            return None
        trash_path = Path(trash_text)
        if trash_path.exists():
            return TrashMove(original=path, trash=trash_path)
    except Exception:
        return None
    return None


def move_to_trash_recorded(path: Path) -> Optional[TrashMove]:
    if not path.exists():
        return None
    try:
        trash_path = unique_path(trash_folder_for_path(path) / path.name)
        shutil.move(str(path), str(trash_path))
        return TrashMove(original=path, trash=trash_path)
    except OSError:
        pass
    finder_move = finder_move_to_trash_recorded(path)
    if finder_move:
        return finder_move
    return None


# ---------------------------------------------------------------------------
# Image, video, and audio fingerprints


def perceptual_image_hash(image, hash_size: int = 8, highfreq_factor: int = 4) -> str:
    """Return a compact DCT perceptual hash without the heavyweight SciPy dependency."""
    import numpy as np
    from PIL import Image

    hash_size = max(2, int(hash_size))
    image_size = hash_size * max(1, int(highfreq_factor))
    resampling = getattr(Image, "Resampling", Image).LANCZOS
    pixels = np.asarray(
        image.convert("L").resize((image_size, image_size), resampling),
        dtype=np.float64,
    )

    # This is the same unnormalised type-II DCT used by imagehash.phash.  Keeping
    # the tiny transform here avoids shipping all of SciPy for one 32x32 matrix.
    samples = np.arange(image_size, dtype=np.float64)
    frequencies = samples[:, None]
    transform = 2.0 * np.cos(
        np.pi * frequencies * (2.0 * samples[None, :] + 1.0) / (2.0 * image_size)
    )
    low_frequencies = (transform @ pixels @ transform.T)[:hash_size, :hash_size]
    bits = (low_frequencies > np.median(low_frequencies)).reshape(-1)
    bit_text = "".join("1" if value else "0" for value in bits)
    width = (len(bit_text) + 3) // 4
    return f"{int(bit_text, 2):0{width}x}"


@dataclass(frozen=True)
class ImageFingerprint:
    phash: str
    average_rgb: Tuple[float, float, float]
    aspect_ratio: float


def image_phash(path: Path) -> Optional[ImageFingerprint]:
    try:
        raise_if_scan_cancelled()
        starting_signature = file_change_signature(path)
        from PIL import Image, ImageStat

        with Image.open(path) as img:
            rgb = img.convert("RGB")
            value = perceptual_image_hash(rgb)
            resampling = getattr(Image, "Resampling", Image).LANCZOS
            color_sample = rgb.resize((32, 32), resampling)
            average_rgb = tuple(float(value) for value in ImageStat.Stat(color_sample).mean[:3])
            aspect_ratio = rgb.width / max(1.0, float(rgb.height))
        raise_if_scan_cancelled()
        if file_change_signature(path) != starting_signature:
            return None
        return ImageFingerprint(value, average_rgb, aspect_ratio)
    except ScanCancelled:
        raise
    except Exception:
        return None


def image_fingerprints_match(left: ImageFingerprint, right: ImageFingerprint) -> bool:
    if hamming_hex(left.phash, right.phash) > 8:
        return False
    aspect_difference = abs(left.aspect_ratio - right.aspect_ratio) / max(
        0.01,
        left.aspect_ratio,
        right.aspect_ratio,
    )
    if aspect_difference > 0.06:
        return False
    color_distance = sum(
        (left_value - right_value) ** 2
        for left_value, right_value in zip(left.average_rgb, right.average_rgb)
    ) ** 0.5
    return color_distance <= 55.0


@dataclass(frozen=True)
class VideoFingerprint:
    duration: float
    timestamps: Tuple[float, ...]
    hashes: Tuple[str, ...]
    average_rgb: Tuple[Tuple[float, float, float], ...]


def cached_scanner_duration(path: Path) -> Optional[float]:
    """Return already-probed scanner metadata without starting another probe."""
    try:
        stat = path.stat()
        cache_key = (str(path), int(stat.st_size), int(stat.st_mtime_ns))
    except OSError:
        return None
    with SCAN_MEDIA_META_LOCK:
        meta = SCAN_MEDIA_META_CACHE.get(cache_key)
    return meta.duration_seconds if meta and meta.duration_seconds > 0 else None


def _video_frame_phashes_uncached(path: Path, samples: int, ffmpeg: str, Image) -> Optional[VideoFingerprint]:
    from PIL import ImageStat

    duration = cached_scanner_duration(path) or ffprobe_duration(path)
    if not duration or duration <= 1:
        return None

    sample_count = max(3, min(7, int(samples)))
    if sample_count <= 3:
        raw_timestamps = [0.35, duration * 0.5, max(0.35, duration - 0.5)]
    elif sample_count <= 5:
        # Beginning/end evidence stays mandatory, but five independent decoder
        # inputs are substantially faster than the accidental seven used before.
        raw_timestamps = [
            0.35,
            duration * 0.25,
            duration * 0.5,
            duration * 0.75,
            max(0.35, duration - 0.5),
        ]
    else:
        raw_timestamps = [
            0.35,
            min(2.0, duration * 0.05),
            duration * 0.25,
            duration * 0.5,
            duration * 0.75,
            max(0.35, duration - 2.0),
            max(0.35, duration - 0.5),
        ]
    timestamps: List[float] = []
    for timestamp in raw_timestamps[:sample_count]:
        timestamp = max(0.2, min(float(timestamp), max(0.2, duration - 0.1)))
        if all(abs(timestamp - existing) > 0.35 for existing in timestamps):
            timestamps.append(timestamp)

    hashes: List[str] = []
    average_colors: List[Tuple[float, float, float]] = []
    successful_timestamps: List[float] = []
    with tempfile.TemporaryDirectory() as td:
        tmpdir = Path(td)
        hwaccel_variants = [ffmpeg_hwaccel_args(), []]
        if not hwaccel_variants[0]:
            hwaccel_variants = [[]]

        frame_paths = [tmpdir / f"frame_{idx}.rgb" for idx in range(len(timestamps))]

        # Starting a decoder process for every timestamp dominated scan time:
        # seven samples across a large folder meant tens of thousands of FFmpeg
        # launches. Reuse one process with one seekable input per sample. This
        # preserves beginning/middle/end evidence while making process startup a
        # once-per-video cost.
        with FINGERPRINT_DIAGNOSTICS_LOCK:
            FINGERPRINT_DIAGNOSTICS["queued"] += 1
        with ScanMediaSlot():
            with FINGERPRINT_DIAGNOSTICS_LOCK:
                FINGERPRINT_DIAGNOSTICS["queued"] -= 1
                FINGERPRINT_DIAGNOSTICS["active"] += 1
                FINGERPRINT_DIAGNOSTICS["peak_active"] = max(
                    FINGERPRINT_DIAGNOSTICS["peak_active"],
                    FINGERPRINT_DIAGNOSTICS["active"],
                )
            try:
                for hwaccel in hwaccel_variants:
                    command = [ffmpeg, "-hide_banner", "-loglevel", "error", "-nostdin", "-y"]
                    for timestamp in timestamps:
                        command.extend(["-ss", str(timestamp), *hwaccel, "-i", str(path)])
                    for input_index, frame_path in enumerate(frame_paths):
                        command.extend(
                            [
                                "-map",
                                f"{input_index}:v:0",
                                "-frames:v",
                                "1",
                                "-vf",
                                "scale=64:64:force_original_aspect_ratio=decrease,"
                                "pad=64:64:(ow-iw)/2:(oh-ih)/2:black",
                                "-pix_fmt",
                                "rgb24",
                                "-f",
                                "rawvideo",
                                str(frame_path),
                            ]
                        )
                    try:
                        timeout_seconds = 30 if sample_count <= 3 else 55
                        result = scan_subprocess_run(
                            command,
                            capture_output=True,
                            timeout=timeout_seconds,
                        )
                    except subprocess.TimeoutExpired:
                        with FINGERPRINT_DIAGNOSTICS_LOCK:
                            FINGERPRINT_DIAGNOSTICS["decoder_timeout"] += 1
                        continue
                    except ScanCancelled:
                        raise
                    except Exception:
                        with FINGERPRINT_DIAGNOSTICS_LOCK:
                            FINGERPRINT_DIAGNOSTICS["decoder_error"] += 1
                        continue
                    if result.returncode == 0 and all(
                        frame_path.exists() and frame_path.stat().st_size == 64 * 64 * 3
                        for frame_path in frame_paths
                    ):
                        break
            finally:
                with FINGERPRINT_DIAGNOSTICS_LOCK:
                    FINGERPRINT_DIAGNOSTICS["active"] -= 1

        for timestamp, frame_path in zip(timestamps, frame_paths):
            if not frame_path.exists() or frame_path.stat().st_size <= 0:
                continue
            try:
                raise_if_scan_cancelled()
                raw_frame = frame_path.read_bytes()
                if len(raw_frame) != 64 * 64 * 3:
                    continue
                image = Image.frombytes("RGB", (64, 64), raw_frame)
                hashes.append(perceptual_image_hash(image))
                average_colors.append(
                    tuple(float(value) for value in ImageStat.Stat(image).mean[:3])
                )
                successful_timestamps.append(timestamp)
            except ScanCancelled:
                raise
            except Exception:
                continue

    if not hashes:
        return None
    return VideoFingerprint(
        float(duration),
        tuple(successful_timestamps),
        tuple(hashes),
        tuple(average_colors),
    )


def video_frame_phashes(path: Path, samples: int = 5) -> Optional[VideoFingerprint]:
    ffmpeg = ffmpeg_path()
    if ffmpeg is None:
        return None

    try:
        from PIL import Image
    except Exception:
        return None

    try:
        starting_signature = file_change_signature(path)
        cache_key = (str(path), *starting_signature, int(samples))
    except OSError:
        return None

    with VIDEO_FINGERPRINT_CACHE_LOCK:
        cached = VIDEO_FINGERPRINT_CACHE.get(cache_key)
        if cached is not None:
            with FINGERPRINT_DIAGNOSTICS_LOCK:
                FINGERPRINT_DIAGNOSTICS["cache_hit"] += 1
            return cached
        pending = VIDEO_FINGERPRINT_INFLIGHT.get(cache_key)
        owns_work = pending is None
        if owns_work:
            pending = concurrent.futures.Future()
            VIDEO_FINGERPRINT_INFLIGHT[cache_key] = pending
            with FINGERPRINT_DIAGNOSTICS_LOCK:
                FINGERPRINT_DIAGNOSTICS["cache_miss"] += 1

    if not owns_work:
        with FINGERPRINT_DIAGNOSTICS_LOCK:
            FINGERPRINT_DIAGNOSTICS["shared_wait"] += 1
        try:
            return wait_for_scan_future(pending, timeout=180)
        except ScanCancelled:
            raise
        except Exception:
            return None

    try:
        fingerprint = _video_frame_phashes_uncached(path, samples, ffmpeg, Image)
    except ScanCancelled:
        with VIDEO_FINGERPRINT_CACHE_LOCK:
            VIDEO_FINGERPRINT_INFLIGHT.pop(cache_key, None)
        if pending is not None and not pending.done():
            pending.set_exception(ScanCancelled())
        raise
    except Exception:
        fingerprint = None

    try:
        if file_change_signature(path) != starting_signature:
            fingerprint = None
    except OSError:
        fingerprint = None

    with VIDEO_FINGERPRINT_CACHE_LOCK:
        if fingerprint is not None:
            if len(VIDEO_FINGERPRINT_CACHE) >= VIDEO_FINGERPRINT_CACHE_LIMIT:
                remove_count = max(1, VIDEO_FINGERPRINT_CACHE_LIMIT // 8)
                for old_key in list(VIDEO_FINGERPRINT_CACHE)[:remove_count]:
                    VIDEO_FINGERPRINT_CACHE.pop(old_key, None)
            VIDEO_FINGERPRINT_CACHE[cache_key] = fingerprint
        VIDEO_FINGERPRINT_INFLIGHT.pop(cache_key, None)
    if pending is not None and not pending.done():
        pending.set_result(fingerprint)
    with FINGERPRINT_DIAGNOSTICS_LOCK:
        FINGERPRINT_DIAGNOSTICS["completed" if fingerprint is not None else "failed"] += 1
    return fingerprint


def video_keyframe_phashes(path: Path, max_frames: int = 240) -> List[str]:
    """Read a compact ordered visual sequence for confirming excerpt matches."""
    ffmpeg = ffmpeg_path()
    if ffmpeg is None:
        return []
    try:
        from PIL import Image
    except Exception:
        return []

    frame_width = 32
    frame_height = 32
    frame_bytes = frame_width * frame_height * 3
    duration = cached_scanner_duration(path) or ffprobe_duration(path) or 0.0
    interval = max(0.25, duration / max(1, max_frames)) if duration > 0 else 0.25
    frame_filter = (
        "select=isnan(prev_selected_t)+"
        f"gte(t-prev_selected_t\\,{interval:.6f}),"
        "scale=32:32:force_original_aspect_ratio=decrease,"
        "pad=32:32:(ow-iw)/2:(oh-ih)/2:black"
    )
    command = [
        ffmpeg,
        "-hide_banner",
        "-loglevel",
        "error",
        "-skip_frame",
        "nokey",
        "-i",
        str(path),
        "-map",
        "0:v:0",
        "-vf",
        frame_filter,
        "-frames:v",
        str(max_frames),
        "-pix_fmt",
        "rgb24",
        "-fps_mode",
        "vfr",
        "-f",
        "rawvideo",
        "pipe:1",
    ]
    try:
        with ScanMediaSlot():
            result = scan_subprocess_run(command, capture_output=True, timeout=150)
    except ScanCancelled:
        raise
    except Exception:
        return []
    if result.returncode != 0 or len(result.stdout) < frame_bytes:
        return []

    frame_count = len(result.stdout) // frame_bytes
    indexes = list(range(frame_count))
    if frame_count > max_frames:
        indexes = sorted({round(index * (frame_count - 1) / (max_frames - 1)) for index in range(max_frames)})

    hashes: List[str] = []
    for index in indexes:
        raise_if_scan_cancelled()
        start = index * frame_bytes
        frame = result.stdout[start : start + frame_bytes]
        try:
            image = Image.frombytes("RGB", (frame_width, frame_height), frame)
            value = perceptual_image_hash(image)
        except Exception:
            continue
        if not hashes or hamming_hex(value, hashes[-1]) > 3:
            hashes.append(value)
    return hashes


def ordered_video_sequence_match(short_hashes: List[str], long_hashes: List[str]) -> bool:
    """Require several distinct frames to reappear in the same temporal order."""
    if len(short_hashes) < 4 or len(long_hashes) < 4:
        return False
    anchor_count = min(9, len(short_hashes))
    anchor_indexes = sorted({round(index * (len(short_hashes) - 1) / (anchor_count - 1)) for index in range(anchor_count)})
    anchors: List[str] = []
    for index in anchor_indexes:
        value = short_hashes[index]
        if not anchors or all(hamming_hex(value, existing) > 4 for existing in anchors):
            anchors.append(value)
    if len(anchors) < 4:
        return False

    required = max(4, int(len(anchors) * 0.80 + 0.999))
    first_candidates = [index for index, value in enumerate(long_hashes) if hamming_hex(anchors[0], value) <= 8]
    for first_index in first_candidates:
        cursor = first_index + 1
        distances = [hamming_hex(anchors[0], long_hashes[first_index])]
        matched_anchor_indexes = [0]
        for anchor_index, anchor in enumerate(anchors[1:], start=1):
            best_index = None
            best_distance = 999999
            for index in range(cursor, len(long_hashes)):
                distance = hamming_hex(anchor, long_hashes[index])
                if distance < best_distance:
                    best_index = index
                    best_distance = distance
                if distance <= 6:
                    break
            if best_index is None or best_distance > 9:
                continue
            distances.append(best_distance)
            matched_anchor_indexes.append(anchor_index)
            cursor = best_index + 1
            if cursor >= len(long_hashes):
                break
        if (
            len(distances) >= required
            and matched_anchor_indexes[-1] == len(anchors) - 1
            and sum(distances) / len(distances) <= 6.5
            and max(distances) <= 9
        ):
            return True
    return False


def audio_signature(path: Path) -> Optional[str]:
    ffmpeg = ffmpeg_path()
    if ffmpeg is None:
        return None

    try:
        import numpy as np
    except Exception:
        return None

    try:
        starting_signature = file_change_signature(path)
        result = scan_subprocess_run(
            [
                ffmpeg,
                "-hide_banner",
                "-loglevel",
                "error",
                "-i",
                str(path),
                "-vn",
                "-ac",
                "1",
                "-ar",
                "16000",
                "-f",
                "s16le",
                "-t",
                "180",
                "pipe:1",
            ],
            capture_output=True,
            timeout=90,
        )
        if result.returncode != 0 or not result.stdout:
            return None

        data = np.frombuffer(result.stdout, dtype=np.int16).astype(np.float32)
        if len(data) < 4000:
            return None

        # Keep the signature at a fixed 192 bits even for short clips. Splitting
        # one or two seconds into 64 raw windows used to make each chunk too
        # small and silently drop the file from deep audio matching.
        minimum_analysis_samples = 64 * 512
        if len(data) < minimum_analysis_samples:
            source_indexes = np.arange(len(data), dtype=np.float32)
            target_indexes = np.linspace(
                0,
                len(data) - 1,
                minimum_analysis_samples,
                dtype=np.float32,
            )
            data = np.interp(target_indexes, source_indexes, data).astype(np.float32)

        windows = 64
        chunks = np.array_split(data, windows)
        energies = []
        centroids = []
        high_ratios = []
        for chunk in chunks:
            raise_if_scan_cancelled()
            if len(chunk) < 512:
                continue
            sample_count = min(8192, len(chunk))
            indexes = np.linspace(0, len(chunk) - 1, sample_count).astype(np.int64)
            sample = chunk[indexes]
            energies.append(float(np.log1p(np.sqrt(np.mean(sample * sample)))))
            windowed = sample * np.hanning(len(sample))
            spectrum = np.abs(np.fft.rfft(windowed)) + 1e-9
            frequencies = np.fft.rfftfreq(len(sample), d=1.0 / 16000.0)
            power_sum = float(np.sum(spectrum))
            centroids.append(float(np.sum(frequencies * spectrum) / power_sum))
            high_ratios.append(float(np.sum(spectrum[frequencies >= 3000]) / power_sum))
        if len(energies) < 32:
            return None

        energy_values = np.asarray(energies, dtype=np.float32)
        centroid_values = np.asarray(centroids, dtype=np.float32)
        high_values = np.asarray(high_ratios, dtype=np.float32)
        energy_deltas = np.diff(energy_values, prepend=energy_values[0])
        bits = "".join("1" if value >= 0 else "0" for value in energy_deltas)
        bits += "".join("1" if value >= np.median(centroid_values) else "0" for value in centroid_values)
        bits += "".join("1" if value >= np.median(high_values) else "0" for value in high_values)
        # Relative medians alone make two steady but completely different tones
        # look identical. Absolute spectral bands preserve where the sound's
        # energy lives while remaining insensitive to volume and most encoding
        # changes.
        for threshold_hz in (250.0, 500.0, 1000.0, 2000.0, 4000.0, 6000.0):
            bits += "".join(
                "1" if value >= threshold_hz else "0"
                for value in centroid_values
            )
        signature = hex(int(bits, 2))[2:].zfill((len(bits) + 3) // 4)
        if file_change_signature(path) != starting_signature:
            return None
        return signature
    except ScanCancelled:
        raise
    except Exception:
        return None


# ---------------------------------------------------------------------------
# File classification and folder metrics


def looks_like_mpeg_transport_stream(data: bytes) -> bool:
    """Recognize MPEG-TS sync bytes without confusing TypeScript source files."""
    if len(data) < 376:
        return False
    for offset in range(min(188, len(data))):
        if data[offset] != 0x47:
            continue
        if offset + 188 < len(data) and data[offset + 188] == 0x47:
            if offset + 376 >= len(data) or data[offset + 376] == 0x47:
                return True
    return False


def bytes_look_like_text(data: bytes) -> bool:
    if not data:
        return False
    encodings = ["utf-8-sig"]
    if data.startswith((b"\xff\xfe", b"\xfe\xff")):
        encodings.insert(0, "utf-16")
    text = ""
    for encoding in encodings:
        try:
            text = data.decode(encoding)
            break
        except UnicodeDecodeError:
            continue
    if not text and b"\x00" not in data:
        candidate = data.decode("utf-8", errors="replace")
        if candidate and candidate.count("\ufffd") / len(candidate) <= 0.01:
            text = candidate
    if not text:
        return False
    readable = sum(character.isprintable() or character in "\r\n\t" for character in text)
    return readable / len(text) >= 0.95


def is_video_path(path: Path, head: Optional[bytes] = None) -> bool:
    suffix = path.suffix.lower()
    if suffix not in VIDEO_EXTS:
        return False
    if suffix != ".ts":
        return True
    if head is None:
        try:
            with path.open("rb") as source:
                head = source.read(4096)
        except OSError:
            # Keep an unreadable .ts in the media validation path so the bad-file
            # scanner reports it rather than treating it as source code.
            return True
    if looks_like_mpeg_transport_stream(head):
        return True
    return not bytes_look_like_text(head)


def is_media_path(path: Path, head: Optional[bytes] = None) -> bool:
    return is_video_path(path, head=head) or path.suffix.lower() in AUDIO_EXTS


def kind_for_path(path: Path) -> str:
    ext = path.suffix.lower()
    if not ext:
        return "No Extension"
    if ext in IMAGE_EXTS:
        return "Image"
    if is_video_path(path):
        return "Video"
    if ext in AUDIO_EXTS:
        return "Audio"
    if ext in DOCUMENT_EXTS:
        return "Document"
    if ext in ARCHIVE_EXTS:
        return "Archive"
    if ext in CODE_EXTS:
        return "Code"
    if ext in DATA_EXTS:
        return "Data"
    return "Other"


def mime_for_path(path: Path) -> str:
    mime, _ = mimetypes.guess_type(path.name)
    return mime or "unknown"


@dataclass
class FileInfo:
    path: Path
    name: str
    extension: str
    kind: str
    mime: str
    size: int
    created: float
    modified: float
    accessed: float
    indexed: bool


@dataclass
class FolderSummary:
    file_count: int
    folder_count: int
    total_size: int
    type_count: int
    indexed_count: int
    largest: Optional[FileInfo]
    oldest: Optional[FileInfo]
    newest: Optional[FileInfo]
    kind_counts: Counter
    kind_sizes: Counter


def file_info(path: Path) -> Optional[FileInfo]:
    try:
        st = path.stat()
        created = mac_creation_time(path)
        modified = st.st_mtime
        accessed = st.st_atime
    except OSError:
        return None

    ext = path.suffix.lower().lstrip(".") or "none"
    return FileInfo(
        path=path,
        name=path.name,
        extension=ext,
        kind=kind_for_path(path),
        mime=mime_for_path(path),
        size=st.st_size,
        created=created,
        modified=modified,
        accessed=accessed,
        indexed=strip_order_prefixes(path.name) != path.name,
    )


def folder_info(path: Path) -> Optional[FileInfo]:
    try:
        st = path.stat()
        created = mac_creation_time(path)
        modified = st.st_mtime
        accessed = st.st_atime
    except OSError:
        return None

    return FileInfo(
        path=path,
        name=path.name,
        extension="folder",
        kind="Folder",
        mime="inode/directory",
        size=st.st_size,
        created=created,
        modified=modified,
        accessed=accessed,
        indexed=False,
    )


def native_folder_apparent_size(path: Path) -> Optional[int]:
    """Use macOS' native directory walker instead of crossing Python per file."""
    if sys.platform != "darwin" or not Path("/usr/bin/du").is_file():
        return None

    command = ["/usr/bin/du", "-A", "-k", "-s"]
    for ignored_name in (
        ".DS_Store",
        ".localized",
        "._*",
        ".fseventsd",
        ".Spotlight-V100",
        ".TemporaryItems",
        ".Trashes",
    ):
        command.extend(("-I", ignored_name))
    command.extend(("--", os.fspath(path)))

    try:
        result = subprocess.run(
            command,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            check=False,
        )
    except (OSError, subprocess.SubprocessError):
        return None

    match = re.match(rb"\s*(\d+)", result.stdout)
    if match is None:
        return None
    return int(match.group(1)) * 1024


def run_folder_metric_command(command: List[str], cancel_event: threading.Event) -> subprocess.CompletedProcess:
    """Run macOS' directory-size helper without trapping the app during exit."""
    if cancel_event.is_set():
        raise FolderMetricCancelled()
    process = subprocess.Popen(
        command,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
    )
    try:
        while True:
            if cancel_event.is_set():
                stop_child_process(process)
                raise FolderMetricCancelled()
            try:
                stdout, _stderr = process.communicate(timeout=0.1)
                if cancel_event.is_set():
                    raise FolderMetricCancelled()
                return subprocess.CompletedProcess(command, process.returncode, stdout, b"")
            except subprocess.TimeoutExpired:
                continue
    finally:
        if cancel_event.is_set():
            stop_child_process(process)
        close_child_process_streams(process)


def cancellable_native_folder_apparent_size(
    path: Path,
    cancel_event: threading.Event,
) -> Optional[int]:
    if sys.platform != "darwin" or not Path("/usr/bin/du").is_file():
        return None
    command = ["/usr/bin/du", "-A", "-k", "-s"]
    for ignored_name in (
        ".DS_Store",
        ".localized",
        "._*",
        ".fseventsd",
        ".Spotlight-V100",
        ".TemporaryItems",
        ".Trashes",
    ):
        command.extend(("-I", ignored_name))
    command.extend(("--", os.fspath(path)))
    result = run_folder_metric_command(command, cancel_event)
    match = re.match(rb"\s*(\d+)", result.stdout)
    return int(match.group(1)) * 1024 if match is not None else None


def native_folder_apparent_sizes(
    paths: Sequence[Path],
    cancel_event: Optional[threading.Event] = None,
) -> Dict[str, int]:
    """Measure sibling folders in one native traversal."""
    normalized_paths = [Path(path) for path in paths]
    if sys.platform != "darwin" or not normalized_paths or not Path("/usr/bin/du").is_file():
        return {}

    command = ["/usr/bin/du", "-A", "-k", "-s"]
    for ignored_name in (
        ".DS_Store",
        ".localized",
        "._*",
        ".fseventsd",
        ".Spotlight-V100",
        ".TemporaryItems",
        ".Trashes",
    ):
        command.extend(("-I", ignored_name))
    command.append("--")
    command.extend(os.fspath(path) for path in normalized_paths)

    try:
        result = (
            run_folder_metric_command(command, cancel_event)
            if cancel_event is not None
            else subprocess.run(
                command,
                stdin=subprocess.DEVNULL,
                stdout=subprocess.PIPE,
                stderr=subprocess.DEVNULL,
                check=False,
            )
        )
    except (OSError, subprocess.SubprocessError):
        return {}

    sizes: Dict[str, int] = {}
    for raw_line in result.stdout.splitlines():
        try:
            block_text, raw_path = raw_line.split(None, 1)
            measured_path = os.path.normpath(os.fsdecode(raw_path))
            sizes[measured_path] = max(0, int(block_text) * 1024)
        except (TypeError, ValueError):
            continue
    return sizes


def scandir_folder_size(path: Path, cancel_event: Optional[threading.Event] = None) -> int:
    """Portable fallback with one directory entry/stat object per file."""
    total_size = 0
    pending = [os.fspath(path)]
    while pending:
        if cancel_event is not None and cancel_event.is_set():
            raise FolderMetricCancelled()
        current = pending.pop()
        try:
            with os.scandir(current) as entries:
                for entry in entries:
                    if cancel_event is not None and cancel_event.is_set():
                        raise FolderMetricCancelled()
                    name = entry.name
                    if name.startswith("._") or name in IGNORED_FILE_NAMES:
                        continue
                    try:
                        if entry.is_dir(follow_symlinks=False):
                            if name not in IGNORED_FOLDER_NAMES:
                                pending.append(entry.path)
                        elif entry.is_file(follow_symlinks=True):
                            total_size += entry.stat(follow_symlinks=True).st_size
                    except OSError:
                        continue
        except OSError:
            continue
    return total_size


def recursive_folder_info(
    path: Path,
    cancel_event: Optional[threading.Event] = None,
) -> Optional[FileInfo]:
    """Compute a folder's useful recursive size away from the GUI thread."""
    try:
        st = path.stat()
    except OSError:
        return None
    total_size = (
        cancellable_native_folder_apparent_size(path, cancel_event)
        if cancel_event is not None
        else native_folder_apparent_size(path)
    )
    if total_size is None:
        total_size = scandir_folder_size(path, cancel_event)
    return FileInfo(
        path=path,
        name=path.name,
        extension="folder",
        kind="Folder",
        mime="inode/directory",
        size=total_size,
        created=mac_creation_time(path),
        modified=st.st_mtime,
        accessed=st.st_atime,
        indexed=False,
    )


def recursive_folder_infos(
    paths: Sequence[Path],
    cancel_event: Optional[threading.Event] = None,
) -> Dict[str, Optional[FileInfo]]:
    """Return recursive metrics for multiple sibling folders without disk thrash."""
    normalized_paths = [Path(path) for path in paths]
    native_sizes = native_folder_apparent_sizes(normalized_paths, cancel_event)
    results: Dict[str, Optional[FileInfo]] = {}
    for path in normalized_paths:
        if cancel_event is not None and cancel_event.is_set():
            raise FolderMetricCancelled()
        path_key = os.path.normpath(os.fspath(path))
        try:
            st = path.stat()
        except OSError:
            results[path_key] = None
            continue
        total_size = native_sizes.get(path_key)
        if total_size is None:
            total_size = scandir_folder_size(path, cancel_event)
        results[path_key] = FileInfo(
            path=path,
            name=path.name,
            extension="folder",
            kind="Folder",
            mime="inode/directory",
            size=total_size,
            created=mac_creation_time(path),
            modified=st.st_mtime,
            accessed=st.st_atime,
            indexed=False,
        )
    return results


class FolderMetricSignals(QObject):
    ready = Signal(str, object)


def scan_folder(folder: Path) -> Tuple[List[FileInfo], FolderSummary]:
    infos = [info for p in list_files(folder) if (info := file_info(p)) is not None]
    infos.sort(key=lambda info: natural_text_key(info.name))
    folders = list_child_folders(folder)
    folder_infos = [info for p in folders if (info := folder_info(p)) is not None]
    entries = infos + folder_infos

    kind_counts: Counter = Counter(info.kind for info in entries)
    kind_sizes: Counter = Counter()
    for info in entries:
        kind_sizes[info.kind] += info.size

    summary = FolderSummary(
        file_count=len(infos),
        folder_count=len(folders),
        total_size=sum(info.size for info in entries),
        type_count=len(kind_counts),
        indexed_count=sum(1 for info in infos if info.indexed),
        largest=max(entries, key=lambda info: info.size, default=None),
        oldest=min(entries, key=lambda info: info.created, default=None),
        newest=max(entries, key=lambda info: info.created, default=None),
        kind_counts=kind_counts,
        kind_sizes=kind_sizes,
    )
    return infos, summary


# ---------------------------------------------------------------------------
# Reusable browser widgets


class SortableItem(QTableWidgetItem):
    def __init__(self, text: str, sort_value=None):
        super().__init__(text)
        self.sort_value = text.casefold() if sort_value is None else sort_value

    def __lt__(self, other):
        if isinstance(other, SortableItem):
            return self.sort_value < other.sort_value
        return super().__lt__(other)


class MetricCard(QFrame):
    clicked = Signal()
    doubleClicked = Signal()

    def __init__(self, title: str, accent: str):
        super().__init__()
        self.setObjectName("MetricCard")
        self.setMinimumHeight(74)
        self.setSizePolicy(QSizePolicy.Fixed, QSizePolicy.Fixed)
        self.clickable = False
        self.elide_meta = False
        self._metric_value_text = "--"
        self._metric_meta_text = ""

        layout = QVBoxLayout(self)
        layout.setContentsMargins(12, 9, 12, 9)
        layout.setSpacing(3)

        self.title = QLabel(title)
        self.title.setObjectName("MetricTitle")
        self.value = QLabel("--")
        self.value.setObjectName("MetricValue")
        self.meta = QLabel("")
        self.meta.setObjectName("MetricMeta")

        for label in (self.title, self.value, self.meta):
            label.setAttribute(Qt.WA_TransparentForMouseEvents, True)

        layout.addWidget(self.title)
        layout.addWidget(self.value)
        layout.addWidget(self.meta)

        self.setStyleSheet(f"""
            QFrame#MetricCard {{
                border-left: 3px solid {accent};
            }}
        """)

    def set_clickable(self, enabled: bool = True):
        self.clickable = enabled
        self.setCursor(Qt.PointingHandCursor if enabled else Qt.ArrowCursor)

    def mouseReleaseEvent(self, event):
        if self.clickable and event.button() == Qt.LeftButton and self.rect().contains(event.pos()):
            self.clicked.emit()
            event.accept()
            return
        super().mouseReleaseEvent(event)

    def mouseDoubleClickEvent(self, event):
        if self.clickable and event.button() == Qt.LeftButton:
            self.doubleClicked.emit()
            event.accept()
            return
        super().mouseDoubleClickEvent(event)

    def set_metric(self, value: str, meta: str = ""):
        self._metric_value_text = value or "--"
        self._metric_meta_text = meta or ""
        self.value.setText(self._metric_value_text)
        self._apply_meta_text()

    def set_meta_elide(self, enabled: bool = True):
        self.elide_meta = enabled
        self._apply_meta_text()

    def _apply_meta_text(self):
        text = self._metric_meta_text
        if self.elide_meta and text:
            width = max(80, self.meta.width() or self.width() - 24)
            text = self.meta.fontMetrics().elidedText(text, Qt.ElideRight, width)
        self.meta.setText(text)
        self.meta.setToolTip(self._metric_meta_text if self._metric_meta_text else "")

    def resizeEvent(self, event):
        super().resizeEvent(event)
        self._apply_meta_text()



class MiniHistogram(QWidget):
    barClicked = Signal(int, str)

    def __init__(self):
        super().__init__()
        self.bins: List[int] = []
        self.bin_labels: List[str] = []
        self.selected_index: Optional[int] = None
        self.setFixedHeight(24)
        self.setMinimumWidth(120)
        self.setMouseTracking(True)
        self.setCursor(Qt.PointingHandCursor)
        self.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)
        self.setToolTip("No size data")

    def set_bins(self, bins: List[int], tooltip: str = "", bin_labels: Optional[List[str]] = None):
        self.bins = list(bins)
        self.bin_labels = list(bin_labels or [])
        self.selected_index = None
        self.setToolTip(tooltip or "No size data")
        self.update()

    def _bar_rects(self) -> List[QRect]:
        rect = self.rect().adjusted(0, 2, 0, -2)
        if not self.bins or rect.width() <= 0:
            return []
        max_value = max(self.bins) or 1
        gap = 5
        count = len(self.bins)
        bar_width = max(2, (rect.width() - gap * (count - 1)) / max(1, count))
        bar_rects: List[QRect] = []
        for index, value in enumerate(self.bins):
            height_ratio = value / max_value
            bar_height = max(2, int(rect.height() * height_ratio)) if value else 2
            x = rect.left() + int(index * (bar_width + gap))
            y = rect.bottom() - bar_height + 1
            bar_rects.append(QRect(int(x), int(y), int(bar_width), int(bar_height)))
        return bar_rects

    def _bar_index_at(self, pos) -> Optional[int]:
        for index, bar_rect in enumerate(self._bar_rects()):
            hit_rect = QRect(bar_rect)
            hit_rect.setTop(0)
            hit_rect.setBottom(self.height())
            if hit_rect.contains(pos):
                return index
        return None

    def mouseMoveEvent(self, event):
        pos = event.position().toPoint() if hasattr(event, "position") else event.pos()
        index = self._bar_index_at(pos)
        if index is not None and index < len(self.bin_labels):
            self.setToolTip(self.bin_labels[index])
        super().mouseMoveEvent(event)

    def mousePressEvent(self, event):
        pos = event.position().toPoint() if hasattr(event, "position") else event.pos()
        if event.button() == Qt.LeftButton:
            index = self._bar_index_at(pos)
            if index is not None and index < len(self.bin_labels):
                self.selected_index = index
                label = self.bin_labels[index]
                self.setToolTip(label)
                self.barClicked.emit(index, label)
                self.update()
                event.accept()
                return
        super().mousePressEvent(event)

    def paintEvent(self, event):
        super().paintEvent(event)
        if not self.bins:
            return
        painter = QPainter(self)
        painter.setRenderHint(QPainter.Antialiasing, True)
        painter.setPen(Qt.NoPen)
        normal_brush = QColor(165, 170, 214)
        selected_brush = QColor(205, 208, 238)
        for index, bar_rect in enumerate(self._bar_rects()):
            painter.setBrush(selected_brush if index == self.selected_index else normal_brush)
            painter.drawRoundedRect(bar_rect, 2, 2)


class StatisticsCard(QFrame):
    def __init__(self, accent: str):
        super().__init__()
        self.setObjectName("MetricCard")
        self.setMinimumHeight(74)
        # The histogram is the flexible metric card: it absorbs any extra
        # horizontal room instead of leaving a blank strip at the right edge.
        self.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)
        self.default_meta = "--"

        layout = QVBoxLayout(self)
        layout.setContentsMargins(12, 8, 12, 8)
        layout.setSpacing(3)

        self.title = QLabel("Statistics")
        self.title.setObjectName("MetricTitle")
        self.histogram = MiniHistogram()
        self.meta = QLabel("--")
        self.meta.setObjectName("MetricMeta")
        self.meta.setMinimumHeight(16)
        self.meta.setWordWrap(False)
        self.meta.setSizePolicy(QSizePolicy.Ignored, QSizePolicy.Fixed)
        self.meta.setToolTip("Click a histogram bar to show that size bucket here")
        self.histogram.barClicked.connect(self.show_bar_statistics)

        layout.addWidget(self.title)
        layout.addWidget(self.histogram)
        layout.addWidget(self.meta)

        self.setStyleSheet(f"""
            QFrame#MetricCard {{
                border-left: 3px solid {accent};
            }}
        """)

    def set_statistics(self, bins: List[int], meta: str, tooltip: str = "", bin_labels: Optional[List[str]] = None):
        self.default_meta = meta or "--"
        self.histogram.set_bins(bins, tooltip, bin_labels)
        self.meta.setText(self.default_meta)
        self.meta.setToolTip("Click a histogram bar to show that size bucket here")

    def show_bar_statistics(self, index: int, label: str):
        self.meta.setText(label)
        self.meta.setToolTip(label)

    def clear_selection(self):
        self.histogram.selected_index = None
        self.histogram.update()
        self.meta.setText(self.default_meta)
        self.meta.setToolTip("Click a histogram bar to show that size bucket here")

    def set_metric(self, value: str, meta: str = ""):
        # Compatibility with the normal MetricCard API used by empty/error states.
        self.default_meta = meta or value or "--"
        self.histogram.set_bins([], meta or value or "No size data")
        self.meta.setText(self.default_meta)
        self.meta.setToolTip(self.default_meta)


class DateRangeCard(QFrame):
    oldestClicked = Signal()
    newestClicked = Signal()

    def __init__(self, accent: str):
        super().__init__()
        self.setObjectName("MetricCard")
        self.setMinimumHeight(74)
        self.setSizePolicy(QSizePolicy.Fixed, QSizePolicy.Fixed)

        layout = QVBoxLayout(self)
        layout.setContentsMargins(12, 8, 12, 8)
        layout.setSpacing(3)

        self.title = QLabel("Date Range")
        self.title.setObjectName("MetricTitle")

        self.start_label = QLabel("--")
        self.start_label.setObjectName("MetricMeta")
        self.start_label.setWordWrap(False)
        self.start_label.setCursor(Qt.PointingHandCursor)
        self.start_label.installEventFilter(self)
        self.end_label = QLabel("--")
        self.end_label.setObjectName("MetricMeta")
        self.end_label.setWordWrap(False)
        self.end_label.setCursor(Qt.PointingHandCursor)
        self.end_label.installEventFilter(self)

        font = self.start_label.font()
        font.setPointSize(max(11, font.pointSize() + 1))
        font.setBold(True)
        self.start_label.setFont(font)
        self.end_label.setFont(font)

        layout.addWidget(self.title)
        layout.addWidget(self.start_label)
        layout.addWidget(self.end_label)
        layout.addStretch(1)

        self.setStyleSheet(f"""
            QFrame#MetricCard {{
                border-left: 3px solid {accent};
            }}
            QLabel#MetricMeta {{
                color: #f1f2f4;
            }}
        """)

    def eventFilter(self, obj, event):
        if event.type() == QEvent.MouseButtonRelease and event.button() == Qt.LeftButton:
            if obj is self.start_label and self.start_label.text().strip() not in {"", "--"}:
                self.oldestClicked.emit()
                return True
            if obj is self.end_label and self.end_label.text().strip() not in {"", "--"}:
                self.newestClicked.emit()
                return True
        if event.type() == QEvent.MouseButtonDblClick and event.button() == Qt.LeftButton:
            if obj is self.start_label and self.start_label.text().strip() not in {"", "--"}:
                self.oldestClicked.emit()
                return True
            if obj is self.end_label and self.end_label.text().strip() not in {"", "--"}:
                self.newestClicked.emit()
                return True
        return super().eventFilter(obj, event)

    def set_range(self, start_text: str, end_text: str, tooltip: str = ""):
        if start_text and end_text and start_text != "--" and end_text != "--":
            self.start_label.setText(f"From  {start_text}")
            self.end_label.setText(f"To      {end_text}")
            self.start_label.setToolTip("Click to order oldest first and select the oldest item")
            self.end_label.setToolTip("Click to order newest first and select the newest item")
            self.setToolTip(tooltip or f"{start_text} to {end_text}")
        else:
            self.start_label.setText("--")
            self.end_label.setText("")
            self.setToolTip(tooltip or "No date range")

    def set_metric(self, value: str, meta: str = ""):
        # Compatibility with MetricCard calls.
        if meta:
            self.start_label.setText(f"From  {value}")
            self.end_label.setText(f"To      {meta}")
            self.setToolTip(f"{value} to {meta}")
        else:
            self.start_label.setText(value or "--")
            self.end_label.setText("")
            self.setToolTip(value or "No date range")


def file_size_histogram(files: List[FileInfo], bin_count: int = 8) -> Tuple[List[int], str, List[str]]:
    sizes = [info.size for info in files if info.size > 0]
    if not sizes:
        return [], "No file sizes", []

    sizes.sort()
    min_size = sizes[0]
    max_size = sizes[-1]
    if min_size == max_size:
        label = f"{human_size(max_size)}: {human_count(len(sizes))} file(s)"
        return [len(sizes)], label, [label]

    # Log-spaced bins keep tiny files and huge videos visible in the same compact spark-histogram.
    import math
    low = math.log10(max(1, min_size))
    high = math.log10(max(1, max_size))
    step = (high - low) / bin_count if bin_count else 1
    bins = [0 for _ in range(bin_count)]
    ranges: List[Tuple[int, int]] = []
    for index in range(bin_count):
        start = int(10 ** (low + step * index))
        end = int(10 ** (low + step * (index + 1))) if index < bin_count - 1 else max_size
        ranges.append((start, end))

    for size in sizes:
        index = int((math.log10(max(1, size)) - low) / step) if step else 0
        index = max(0, min(bin_count - 1, index))
        bins[index] += 1

    bin_labels = [
        f"{human_size(start)} – {human_size(end)}: {human_count(count)} file(s)"
        for (start, end), count in zip(ranges, bins)
    ]
    return bins, "\n".join(bin_labels), bin_labels


def file_size_stats_text(files: List[FileInfo]) -> str:
    sizes = sorted(info.size for info in files if info.size > 0 and not info.path.is_dir())
    if not sizes:
        return "No size stats"
    total = len(sizes)
    median = sizes[total // 2] if total % 2 else int((sizes[total // 2 - 1] + sizes[total // 2]) / 2)
    return f"{human_count(total)} files • median {human_size(median)} • max {human_size(sizes[-1])}"


def compact_date_range_text(oldest: FileInfo, newest: FileInfo) -> Tuple[str, str]:
    start = datetime.fromtimestamp(oldest.created)
    end = datetime.fromtimestamp(newest.created)
    # Return both endpoints separately so the date-range card can render them with equal visual weight.
    return start.strftime('%b %d, %Y'), end.strftime('%b %d, %Y')

class DetailRow(QWidget):
    clicked = Signal()

    def __init__(self, label: str):
        super().__init__()
        self.full_value = "--"
        self.clickable = False
        self.setFixedHeight(27)
        layout = QHBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(8)

        self.label = QLabel(label)
        self.label.setObjectName("DetailLabel")
        self.label.setFixedWidth(92)
        self.value = QLabel("--")
        self.value.setObjectName("DetailValue")
        self.value.setTextInteractionFlags(Qt.TextSelectableByMouse)
        self.value.setWordWrap(False)
        self.value.setFixedHeight(24)
        self.value.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)

        layout.addWidget(self.label)
        layout.addWidget(self.value, stretch=1)

    def set_clickable(self, enabled: bool = True):
        self.clickable = enabled
        self.setCursor(Qt.PointingHandCursor if enabled else Qt.ArrowCursor)
        self.value.setCursor(Qt.PointingHandCursor if enabled else Qt.IBeamCursor)
        self.label.setAttribute(Qt.WA_TransparentForMouseEvents, enabled)
        self.value.setAttribute(Qt.WA_TransparentForMouseEvents, enabled)

    def mouseReleaseEvent(self, event):
        if self.clickable and event.button() == Qt.LeftButton and self.rect().contains(event.pos()):
            self.clicked.emit()
            event.accept()
            return
        super().mouseReleaseEvent(event)

    def set_value(self, value: str):
        self.full_value = value or "--"
        self.value.setToolTip(self.full_value if self.full_value != "--" else "")
        width = max(96, self.value.width() or 240)
        self.value.setText(self.value.fontMetrics().elidedText(self.full_value, Qt.ElideMiddle, width))

    def set_label(self, label: str):
        self.label.setText(label)

    def resizeEvent(self, event):
        super().resizeEvent(event)
        self.set_value(self.full_value)


# ---------------------------------------------------------------------------
# Background preview preparation


class PreviewPlayableProxyWorker(PreviewProcessWorker):
    """Build a buffered Qt-friendly H.264/AAC proxy for unsupported codecs."""
    ready = Signal(int, str)
    bufferExtended = Signal(int, str, int)
    finalized = Signal(int, str)
    failed = Signal(int)
    progress = Signal(int, str)

    def __init__(self, request_id: int, path: Path, surface: str = "unknown"):
        super().__init__()
        self.request_id = request_id
        self.path = Path(path)
        self.surface = str(surface or "unknown")
        self._source_has_audio_expected: Optional[bool] = None

    def proxy_validation_cache_key(self, candidate: Path) -> Optional[Tuple[object, ...]]:
        """Return a rename-stable identity for a source/proxy pair.

        The progressive temporary is atomically renamed to the final cache
        path after validation.  Device/inode/size/mtime survive that rename,
        allowing the other preview surface to trust the exact bytes already
        decoded without launching another 3-5 probe processes.
        """
        source_identity = preview_file_identity(self.path)
        if source_identity is None:
            return None
        try:
            stat = candidate.stat()
        except OSError:
            return None
        if not candidate.is_file() or int(stat.st_size) <= 1024:
            return None
        return (
            source_identity,
            int(getattr(stat, "st_dev", 0)),
            int(getattr(stat, "st_ino", 0)),
            int(stat.st_size),
            int(getattr(stat, "st_mtime_ns", int(stat.st_mtime * 1_000_000_000))),
        )

    @staticmethod
    def proxy_validation_cache_hit(key: Optional[Tuple[object, ...]]) -> bool:
        if key is None:
            return False
        with PREVIEW_PROXY_VALIDATION_CACHE_LOCK:
            return key in PREVIEW_PROXY_VALIDATION_CACHE

    @staticmethod
    def remember_proxy_validation(key: Optional[Tuple[object, ...]]):
        if key is None:
            return
        with PREVIEW_PROXY_VALIDATION_CACHE_LOCK:
            PREVIEW_PROXY_VALIDATION_CACHE[key] = time.monotonic()
            while len(PREVIEW_PROXY_VALIDATION_CACHE) > PREVIEW_PROXY_VALIDATION_CACHE_LIMIT:
                PREVIEW_PROXY_VALIDATION_CACHE.pop(next(iter(PREVIEW_PROXY_VALIDATION_CACHE)))

    def source_has_audio(self, ffmpeg: str, ffprobe: Optional[str]) -> bool:
        if self._source_has_audio_expected is not None:
            return self._source_has_audio_expected
        has_audio = False
        if ffprobe:
            try:
                result = self.run_subprocess(
                    [
                        ffprobe,
                        "-v", "error",
                        "-select_streams", "a:0",
                        "-show_entries", "stream=index",
                        "-of", "csv=p=0",
                        str(self.path),
                    ],
                    timeout=20,
                    text=True,
                    capture_output=True,
                )
                has_audio = result.returncode == 0 and bool(str(result.stdout or "").strip())
            except (OSError, subprocess.SubprocessError):
                has_audio = False
        else:
            try:
                result = self.run_subprocess(
                    [
                        ffmpeg, "-hide_banner", "-loglevel", "error", "-nostdin",
                        "-i", str(self.path), "-map", "0:a:0", "-t", "0.1",
                        "-f", "null", "-",
                    ],
                    timeout=20,
                    text=True,
                    capture_output=True,
                )
                has_audio = result.returncode == 0
            except (OSError, subprocess.SubprocessError):
                has_audio = False
        self._source_has_audio_expected = bool(has_audio)
        return self._source_has_audio_expected

    def proxy_is_playable(
        self,
        candidate: Path,
        ffmpeg: str,
        ffprobe: Optional[str],
    ) -> bool:
        """Require a real, decodable video stream before trusting a proxy.

        Older builds accepted any MP4 larger than 1 KiB.  Because the video
        input map was optional, a failed video conversion could leave an
        audio-only MP4 in the cache and every later preview would remain black.
        """
        validation_key = self.proxy_validation_cache_key(candidate)
        if validation_key is None:
            return False
        if self.proxy_validation_cache_hit(validation_key):
            return True

        require_audio = self.source_has_audio(ffmpeg, ffprobe)
        if ffprobe:
            try:
                probe_result = self.run_subprocess(
                    [
                        ffprobe,
                        "-v", "error",
                        "-select_streams", "v:0",
                        "-show_entries", "stream=codec_name,width,height",
                        "-of", "csv=p=0",
                        str(candidate),
                    ],
                    timeout=20,
                    text=True,
                    capture_output=True,
                )
                probe_line = str(probe_result.stdout or "").strip()
                if probe_result.returncode != 0 or not probe_line:
                    return False
                values = [value.strip() for value in probe_line.split(",")]
                if len(values) < 3 or int(values[-2]) <= 0 or int(values[-1]) <= 0:
                    return False
                if require_audio:
                    audio_probe = self.run_subprocess(
                        [
                            ffprobe,
                            "-v", "error",
                            "-select_streams", "a:0",
                            "-show_entries", "stream=codec_name,channels,sample_rate",
                            "-of", "csv=p=0",
                            str(candidate),
                        ],
                        timeout=20,
                        text=True,
                        capture_output=True,
                    )
                    if audio_probe.returncode != 0 or not str(audio_probe.stdout or "").strip():
                        return False
            except (OSError, ValueError, subprocess.SubprocessError):
                return False

        try:
            decode_result = self.run_subprocess(
                [
                    ffmpeg,
                    "-hide_banner", "-loglevel", "error", "-nostdin",
                    "-i", str(candidate),
                    "-map", "0:v:0",
                    "-frames:v", "1",
                    "-f", "null", "-",
                ],
                timeout=30,
                text=True,
                capture_output=True,
            )
            if decode_result.returncode != 0:
                return False
            if require_audio:
                audio_decode = self.run_subprocess(
                    [
                        ffmpeg,
                        "-hide_banner", "-loglevel", "error", "-nostdin",
                        "-i", str(candidate),
                        "-map", "0:a:0",
                        "-t", "0.5",
                        "-f", "null", "-",
                    ],
                    timeout=30,
                    text=True,
                    capture_output=True,
                )
                if audio_decode.returncode != 0:
                    return False
            self.remember_proxy_validation(validation_key)
            return True
        except (OSError, subprocess.SubprocessError):
            return False

    @staticmethod
    def discard_invalid_proxy(candidate: Path):
        try:
            candidate.unlink(missing_ok=True)
        except OSError:
            pass

    @staticmethod
    def create_proxy_lock(lock_path: Path, token: str) -> bool:
        """Atomically claim a cross-process conversion lock."""
        try:
            descriptor = os.open(
                lock_path,
                os.O_CREAT | os.O_EXCL | os.O_WRONLY,
                0o600,
            )
        except FileExistsError:
            return False
        try:
            os.write(descriptor, token.encode("ascii", errors="strict"))
            try:
                os.fsync(descriptor)
            except OSError:
                pass
        except Exception:
            os.close(descriptor)
            try:
                lock_path.unlink(missing_ok=True)
            except OSError:
                pass
            raise
        os.close(descriptor)
        return True

    @staticmethod
    def proxy_lock_token(lock_path: Path) -> Optional[str]:
        try:
            token = lock_path.read_text(encoding="ascii", errors="strict").strip()
        except (OSError, UnicodeError):
            return None
        return token or None

    @classmethod
    def owns_proxy_lock(cls, lock_path: Path, token: Optional[str]) -> bool:
        return bool(token and cls.proxy_lock_token(lock_path) == token)

    @classmethod
    def heartbeat_proxy_lock(cls, lock_path: Path, token: Optional[str]) -> bool:
        """Refresh only the caller's lock; never touch a replacement owner."""
        if not cls.owns_proxy_lock(lock_path, token):
            return False
        try:
            os.utime(lock_path, None)
        except OSError:
            return False
        return cls.owns_proxy_lock(lock_path, token)

    @classmethod
    def release_proxy_lock(cls, lock_path: Path, token: Optional[str]) -> bool:
        """Remove the lock only when its ownership token still matches."""
        if not cls.owns_proxy_lock(lock_path, token):
            return False
        try:
            lock_path.unlink(missing_ok=True)
            return True
        except OSError:
            return False

    @classmethod
    def remove_stale_proxy_lock(cls, lock_path: Path, stale_seconds: float = 120.0) -> bool:
        """Best-effort stale recovery guarded by an unchanged owner token."""
        observed_token = cls.proxy_lock_token(lock_path)
        if not observed_token:
            return False
        try:
            observed_mtime_ns = int(lock_path.stat().st_mtime_ns)
            age = time.time() - (observed_mtime_ns / 1_000_000_000.0)
        except OSError:
            return False
        if age <= max(1.0, float(stale_seconds)):
            return False
        # Re-read after stat so a heartbeat/replacement observed during the
        # check prevents us from deleting that active owner's file.
        if cls.proxy_lock_token(lock_path) != observed_token:
            return False
        try:
            if int(lock_path.stat().st_mtime_ns) != observed_mtime_ns:
                return False
        except OSError:
            return False
        return cls.release_proxy_lock(lock_path, observed_token)

    def source_duration_seconds(self, ffprobe: Optional[str]) -> float:
        if not ffprobe:
            return 0.0
        try:
            result = self.run_subprocess(
                [
                    ffprobe,
                    "-v", "error",
                    "-show_entries", "format=duration",
                    "-of", "default=noprint_wrappers=1:nokey=1",
                    str(self.path),
                ],
                timeout=20,
                text=True,
                capture_output=True,
            )
            if result.returncode == 0:
                return max(0.0, float(str(result.stdout or "").strip()))
        except (OSError, ValueError, subprocess.SubprocessError):
            pass
        return 0.0

    @staticmethod
    def progressive_buffer_is_sustainable(
        duration_seconds: float,
        buffered_seconds: float,
        encode_speed: float,
        safety_seconds: float = 2.0,
    ) -> bool:
        """Whether a growing proxy has a stable lead over real-time playback.

        An encoder that is comfortably faster than 1x keeps increasing its
        lead while the user watches.  Requiring the *entire* remaining encode
        time to fit inside the current prefix delayed a measured 4K preview by
        twelve seconds even though VideoToolbox was running at 4x.  Keep a
        duration-aware startup cushion for that common case; slower/variable
        encoders retain the conservative finish-before-edge calculation.  The
        caller supplies the slower of the lifetime and recent-window speeds so
        one fast opening burst cannot hide a later encoder slowdown.
        """
        duration = max(0.0, float(duration_seconds or 0.0))
        buffered = max(0.0, float(buffered_seconds or 0.0))
        speed = max(0.0, float(encode_speed or 0.0))
        if duration <= 0.0 or buffered < 6.0 or speed < 1.15:
            return False
        required_buffer = max(10.0, min(20.0, duration * 0.05))
        if buffered >= required_buffer and speed >= 1.5:
            return True
        remaining_wall = max(0.0, duration - buffered) / max(0.01, speed)
        return remaining_wall + max(0.0, float(safety_seconds)) <= buffered

    @staticmethod
    def transcode_progress_seconds(progress_path: Path) -> float:
        """Read FFmpeg's latest privacy-safe encoded timestamp."""
        try:
            text = progress_path.read_text(encoding="utf-8", errors="ignore")
        except OSError:
            return 0.0
        matches = re.findall(r"(?m)^out_time_us=(\d+)\s*$", text)
        if matches:
            try:
                return max(0.0, int(matches[-1]) / 1_000_000.0)
            except ValueError:
                return 0.0
        clock_matches = re.findall(r"(?m)^out_time=(\d+):(\d+):(\d+(?:\.\d+)?)\s*$", text)
        if not clock_matches:
            return 0.0
        hours, minutes, seconds = clock_matches[-1]
        try:
            return int(hours) * 3600.0 + int(minutes) * 60.0 + float(seconds)
        except ValueError:
            return 0.0

    def run_progressive_subprocess(
        self,
        command,
        *,
        timeout: float,
        poll_callback: Callable[[], None],
    ) -> subprocess.CompletedProcess:
        """Run FFmpeg cancellably while allowing a buffered preview handoff."""
        if self.isInterruptionRequested():
            raise PreviewWorkerCancelled()
        with tempfile.TemporaryFile(mode="w+t", encoding="utf-8") as error_output:
            process = subprocess.Popen(
                command,
                stdin=subprocess.DEVNULL,
                stdout=subprocess.DEVNULL,
                stderr=error_output,
                text=True,
            )
            with self._process_lock:
                self._process = process
            deadline = time.monotonic() + max(1.0, float(timeout))
            try:
                while process.poll() is None:
                    if self.isInterruptionRequested():
                        self._stop_process(process)
                        raise PreviewWorkerCancelled()
                    if time.monotonic() >= deadline:
                        self._stop_process(process)
                        raise subprocess.TimeoutExpired(command, timeout)
                    try:
                        poll_callback()
                    except (OSError, RuntimeError, TypeError, ValueError):
                        pass
                    time.sleep(0.05)
                if self.isInterruptionRequested():
                    raise PreviewWorkerCancelled()
                try:
                    poll_callback()
                except (OSError, RuntimeError, TypeError, ValueError):
                    pass
                if self.isInterruptionRequested():
                    raise PreviewWorkerCancelled()
                error_output.flush()
                error_output.seek(0)
                return subprocess.CompletedProcess(
                    command,
                    int(process.returncode or 0),
                    "",
                    error_output.read(),
                )
            finally:
                with self._process_lock:
                    if self._process is process:
                        self._process = None
                close_child_process_streams(process)

    def execute(self):
        temporary = None
        progress_path = None
        lock_path = None
        lock_token = None
        owns_lock = False
        exposed_temporaries: set = set()
        attempt_temporaries: List[Path] = []
        attempt_progress_paths: List[Path] = []
        attempts = 0
        diagnostic = {
            "request_id": self.request_id,
            "item_id": preview_item_id(self.path),
            "extension": self.path.suffix.lower() or "none",
            "surface": self.surface,
        }
        try:
            identity = preview_file_identity(self.path)
            ffmpeg = ffmpeg_path()
            ffprobe = ffprobe_path()
            try:
                source_bytes = self.path.stat().st_size if self.path.exists() else -1
            except OSError:
                source_bytes = -1
            debug_log(
                "media-proxy",
                "compatible preview proxy build started",
                force=True,
                suffix=self.path.suffix.lower() or "none",
                source_exists=self.path.exists(),
                source_bytes=source_bytes,
                identity_ok=identity is not None,
                ffmpeg_available=bool(ffmpeg),
                ffmpeg_binary=(Path(ffmpeg).name if ffmpeg else "none"),
                source_kind="original media",
                decision="inspect validated proxy cache or build",
                **diagnostic,
            )
            if identity is None:
                debug_log(
                    "media-proxy",
                    "compatible preview proxy failed",
                    force=True,
                    reason="source identity unavailable",
                    source_kind="original media",
                    decision="cannot identify input",
                    **diagnostic,
                )
                self.failed.emit(self.request_id)
                return
            if not ffmpeg:
                debug_log(
                    "media-proxy",
                    "compatible preview proxy failed",
                    force=True,
                    reason="ffmpeg executable unavailable",
                    hint="install ffmpeg or package the ffmpeg binary",
                    source_kind="original media",
                    decision="proxy builder unavailable",
                    **diagnostic,
                )
                self.failed.emit(self.request_id)
                return
            key = hashlib.sha1((repr(identity) + "|qt-playable-v7-progressive-audio").encode("utf-8")).hexdigest()
            cache_dir = Path(tempfile.gettempdir()) / "folder_manager_playable_previews"
            cache_dir.mkdir(parents=True, exist_ok=True)
            maintain_preview_cache(
                cache_dir,
                suffix=(".mp4", ".ts"),
                max_files=96,
                keep_files=72,
                max_bytes=2 * 1024 * 1024 * 1024,
            )
            target = cache_dir / f"{key}.ts"
            if self.proxy_is_playable(target, ffmpeg, ffprobe):
                try:
                    os.utime(target, None)
                except OSError:
                    pass
                debug_log(
                    "media-proxy",
                    "compatible preview proxy cache hit",
                    force=True,
                    output_bytes=target.stat().st_size,
                    source_kind="cache",
                    decision="validated cache hit",
                    **diagnostic,
                )
                self.ready.emit(self.request_id, str(target))
                return
            self.discard_invalid_proxy(target)
            debug_log(
                "media-proxy",
                "compatible preview proxy cache miss",
                source_kind="cache",
                decision="missing or rejected; build required",
                **diagnostic,
            )

            # Embedded and Space-triggered previews may request the same proxy.
            # Only one worker owns the conversion; the other reuses its result.
            lock_path = cache_dir / f".{key}.lock"
            lock_token = uuid.uuid4().hex
            wait_started = time.monotonic()
            next_wait_progress_at = wait_started
            while True:
                if self.isInterruptionRequested():
                    raise PreviewWorkerCancelled()
                if self.create_proxy_lock(lock_path, lock_token):
                    owns_lock = True
                    break
                if self.remove_stale_proxy_lock(lock_path):
                    continue
                if target.exists():
                    if self.proxy_is_playable(target, ffmpeg, ffprobe):
                        debug_log(
                            "media-proxy",
                            "compatible preview proxy shared cache ready",
                            force=True,
                            output_bytes=target.stat().st_size,
                            source_kind="shared cache",
                            decision="validated after waiting for another preview",
                            **diagnostic,
                        )
                        self.ready.emit(self.request_id, str(target))
                        return
                    self.discard_invalid_proxy(target)
                now = time.monotonic()
                if now - wait_started > 9 * 60:
                    debug_log(
                        "media-proxy",
                        "compatible preview proxy wait expired",
                        force=True,
                        source_kind="shared conversion",
                        decision="shared conversion timeout",
                        **diagnostic,
                    )
                    self.failed.emit(self.request_id)
                    return
                # This signal crosses into the GUI thread.  Emitting it ten
                # times per second made a second preview window needlessly
                # repaint while it waited for the same conversion.
                if now >= next_wait_progress_at:
                    self.progress.emit(
                        self.request_id,
                        "Preparing compatible video preview (shared conversion)…",
                    )
                    next_wait_progress_at = now + 2.0
                time.sleep(0.1)

            if self.proxy_is_playable(target, ffmpeg, ffprobe):
                debug_log(
                    "media-proxy",
                    "compatible preview proxy cache became ready",
                    force=True,
                    output_bytes=target.stat().st_size,
                    source_kind="cache",
                    decision="validated after lock acquisition",
                    **diagnostic,
                )
                self.ready.emit(self.request_id, str(target))
                return
            self.discard_invalid_proxy(target)
            if not self.heartbeat_proxy_lock(lock_path, lock_token):
                raise PreviewWorkerCancelled()
            duration_seconds = self.source_duration_seconds(ffprobe)
            transcode_timeout = (
                max(180.0, min(3600.0, duration_seconds * 2.0 + 90.0))
                if duration_seconds > 0.0
                else 600.0
            )
            codec_variants = [
                ("h264_videotoolbox", ["-c:v", "h264_videotoolbox", "-b:v", "8M"]),
                ("libx264", ["-c:v", "libx264", "-preset", "veryfast", "-crf", "20"]),
                ("mpeg4", ["-c:v", "mpeg4", "-q:v", "3"]),
            ]
            for codec_name, codec_args in codec_variants:
                attempts += 1
                # Never truncate or reuse a path already handed to Qt.  A
                # hardware encoder can publish a safe prefix and still fail
                # later; the software fallback must write a different inode.
                attempt_id = uuid.uuid4().hex
                temporary = cache_dir / f".{key}.{attempt_id}.ts"
                progress_path = cache_dir / f".{key}.{attempt_id}.progress"
                attempt_temporaries.append(temporary)
                attempt_progress_paths.append(progress_path)
                progressive_ready_emitted = False
                last_buffer_update_seconds = 0.0
                last_buffer_update_at = 0.0
                recent_progress_samples: deque = deque()
                self.progress.emit(
                    self.request_id,
                    f"Preparing compatible video preview ({codec_name}, attempt {attempts}/3)…",
                )
                command = [
                    ffmpeg, "-hide_banner", "-loglevel", "error", "-nostdin",
                    "-stats_period", "0.1", "-progress", str(progress_path), "-nostats",
                    "-y", "-i", str(self.path),
                    # Video is mandatory. Audio remains optional so silent
                    # clips work, but an audio-only proxy can never be cached.
                    "-map", "0:v:0", "-map", "0:a:0?",
                    *codec_args, "-pix_fmt", "yuv420p",
                    "-c:a", "aac", "-b:a", "192k", "-ac", "2",
                    # MPEG-TS is readable while it is still growing. Once the
                    # encoder has produced enough media to finish faster than
                    # the player can consume that buffered lead, the GUI can
                    # start immediately and rebind to the completed cache later.
                    "-f", "mpegts", "-mpegts_flags", "+resend_headers",
                    "-muxdelay", "0", "-flush_packets", "1", str(temporary),
                ]
                started = time.monotonic()
                last_lock_heartbeat_at = started

                def publish_when_safely_buffered():
                    nonlocal progressive_ready_emitted, last_buffer_update_seconds
                    nonlocal last_buffer_update_at, last_lock_heartbeat_at
                    if self.isInterruptionRequested():
                        return
                    now = time.monotonic()
                    if now - last_lock_heartbeat_at >= 1.0:
                        if not self.heartbeat_proxy_lock(lock_path, lock_token):
                            self.requestInterruption()
                            return
                        last_lock_heartbeat_at = now
                    try:
                        output_bytes = temporary.stat().st_size
                    except OSError:
                        return
                    media_seconds = self.transcode_progress_seconds(progress_path)
                    wall_seconds = max(0.05, now - started)
                    encode_speed = media_seconds / wall_seconds
                    recent_progress_samples.append((now, media_seconds))
                    while (
                        len(recent_progress_samples) > 1
                        and now - recent_progress_samples[0][0] > 2.0
                    ):
                        recent_progress_samples.popleft()
                    recent_encode_speed = 0.0
                    if len(recent_progress_samples) > 1:
                        recent_wall = now - recent_progress_samples[0][0]
                        if recent_wall >= 1.25:
                            recent_encode_speed = max(
                                0.0,
                                (media_seconds - recent_progress_samples[0][1]) / recent_wall,
                            )
                    stable_encode_speed = min(encode_speed, recent_encode_speed)
                    if progressive_ready_emitted:
                        # Fast encoders can advance five media seconds several
                        # times per wall-clock second.  Rebinding is a GUI-thread
                        # operation, so rate-limit the cross-thread notification.
                        if (
                            media_seconds >= last_buffer_update_seconds + 5.0
                            and now - last_buffer_update_at >= 1.0
                        ):
                            last_buffer_update_seconds = media_seconds
                            last_buffer_update_at = now
                            self.bufferExtended.emit(
                                self.request_id,
                                str(temporary),
                                max(0, int(media_seconds * 1000.0)),
                            )
                        return
                    if output_bytes < 256 * 1024 or media_seconds < 6.0:
                        return
                    if duration_seconds > 0.0:
                        remaining_wall = max(0.0, duration_seconds - media_seconds) / max(0.01, encode_speed)
                    else:
                        remaining_wall = -1.0
                    # Qt treats the currently written MPEG-TS prefix as a
                    # complete, fixed-duration file.  Publish after a stable
                    # real-time lead exists; buffer-growth callbacks refresh the
                    # source well before its temporary edge.  A marginally slow
                    # encoder still waits until its existing lead can cover the
                    # remaining work. Unknown-duration sources wait for final.
                    if not self.progressive_buffer_is_sustainable(
                        duration_seconds,
                        media_seconds,
                        stable_encode_speed,
                    ):
                        return
                    progressive_ready_emitted = True
                    last_buffer_update_seconds = media_seconds
                    last_buffer_update_at = now
                    debug_log(
                        "media-proxy",
                        "buffered compatibility preview ready before conversion finished",
                        force=True,
                        codec=codec_name,
                        buffered_seconds=f"{media_seconds:.2f}",
                        encode_speed=f"{encode_speed:.2f}x",
                        recent_encode_speed=f"{recent_encode_speed:.2f}x",
                        estimated_remaining_seconds=(
                            f"{remaining_wall:.2f}" if remaining_wall >= 0.0 else "unknown"
                        ),
                        output_bytes=output_bytes,
                        source_kind="growing compatibility proxy",
                        decision="start buffered playback while conversion continues",
                        **diagnostic,
                    )
                    self.progress.emit(
                        self.request_id,
                        "Buffered compatible preview ready; finishing cache in background…",
                    )
                    exposed_temporaries.add(temporary)
                    self.ready.emit(self.request_id, str(temporary))

                try:
                    result = self.run_progressive_subprocess(
                        command,
                        timeout=transcode_timeout,
                        poll_callback=publish_when_safely_buffered,
                    )
                    if not self.heartbeat_proxy_lock(lock_path, lock_token):
                        raise PreviewWorkerCancelled()
                    elapsed = time.monotonic() - started
                    stderr_text = _clean_process_diagnostic(result.stderr, self.path, temporary, target)
                    output_bytes = temporary.stat().st_size if temporary.exists() else 0
                    debug_log(
                        "media-proxy",
                        "ffmpeg proxy attempt finished",
                        force=True,
                        codec=codec_name,
                        returncode=result.returncode,
                        seconds=f"{elapsed:.2f}",
                        output_bytes=output_bytes,
                        stderr=stderr_text,
                        encoder=codec_name,
                        source_kind="temporary proxy",
                        decision="encoder attempt completed",
                        **diagnostic,
                    )
                except subprocess.TimeoutExpired:
                    debug_log(
                        "media-proxy",
                        "ffmpeg proxy attempt failed",
                        force=True,
                        codec=codec_name,
                        reason=f"timeout after {transcode_timeout:.0f}s",
                        encoder=codec_name,
                        source_kind="temporary proxy",
                        decision="encoder timed out",
                        **diagnostic,
                    )
                    continue
                except PreviewWorkerCancelled:
                    raise
                except Exception as exc:
                    debug_log(
                        "media-proxy",
                        "ffmpeg proxy attempt failed",
                        force=True,
                        codec=codec_name,
                        reason=type(exc).__name__,
                        error=str(exc)[:500],
                        encoder=codec_name,
                        source_kind="temporary proxy",
                        decision="encoder raised an exception",
                        **diagnostic,
                    )
                    continue
                if (
                    result.returncode == 0
                    and self.proxy_is_playable(temporary, ffmpeg, ffprobe)
                ):
                    if not self.owns_proxy_lock(lock_path, lock_token):
                        raise PreviewWorkerCancelled()
                    temporary.replace(target)
                    debug_log(
                        "media-proxy",
                        "compatible preview proxy build succeeded",
                        force=True,
                        codec=codec_name,
                        output_bytes=target.stat().st_size,
                        attempts=attempts,
                        encoder=codec_name,
                        source_kind="new validated proxy",
                        decision="proxy built and frame-decode validated",
                        **diagnostic,
                    )
                    if progressive_ready_emitted:
                        self.finalized.emit(self.request_id, str(target))
                    else:
                        self.ready.emit(self.request_id, str(target))
                    return
            debug_log(
                "media-proxy",
                "compatible preview proxy failed",
                force=True,
                reason="all encoder attempts failed",
                attempts=attempts,
                source_kind="temporary proxy",
                decision="no encoder produced a validated video stream",
                **diagnostic,
            )
            self.failed.emit(self.request_id)
        except PreviewWorkerCancelled:
            debug_log(
                "media-proxy",
                "compatible preview proxy cancelled",
                force=True,
                source_kind="proxy worker",
                decision="selection changed or preview closed",
                **diagnostic,
            )
            return
        except Exception as exc:
            debug_log(
                "media-proxy",
                "compatible preview proxy failed",
                force=True,
                reason="worker exception",
                error_type=type(exc).__name__,
                error=str(exc)[:800],
                stack=_short_stack_summary(),
                source_kind="proxy worker",
                decision="worker exception",
                **diagnostic,
            )
            self.failed.emit(self.request_id)
        finally:
            for attempt_temporary in attempt_temporaries:
                if attempt_temporary in exposed_temporaries:
                    continue
                try:
                    attempt_temporary.unlink(missing_ok=True)
                except OSError:
                    pass
            for attempt_progress_path in attempt_progress_paths:
                try:
                    attempt_progress_path.unlink(missing_ok=True)
                except OSError:
                    pass
            if owns_lock and lock_path is not None:
                self.release_proxy_lock(lock_path, lock_token)


class PreviewThumbnailWorker(PreviewProcessWorker):
    loaded = Signal(int, bytes)
    failed = Signal(int)

    def __init__(self, request_id: int, path: Path):
        super().__init__()
        self.request_id = request_id
        self.path = path

    def execute(self):
        temporary: Optional[Path] = None
        try:
            if self.isInterruptionRequested():
                raise PreviewWorkerCancelled()
            identity = preview_file_identity(self.path)
            if identity is None:
                self.failed.emit(self.request_id)
                return
            key = hashlib.sha1(repr(identity).encode("utf-8")).hexdigest()
            cache_dir = Path(tempfile.gettempdir()) / "folder_manager_previews"
            cache_dir.mkdir(parents=True, exist_ok=True)
            maintain_preview_cache(cache_dir)
            target = cache_dir / f"{key}.jpg"
            with PreviewCacheKeySlot(key, self):
                if not target.exists() or target.stat().st_size == 0:
                    temporary = cache_dir / f".{key}.{uuid.uuid4().hex}.jpg"
                    suffix = self.path.suffix.lower()
                    if suffix in IMAGE_EXTS:
                        try:
                            from PIL import Image, ImageOps

                            with Image.open(self.path) as image:
                                image = ImageOps.exif_transpose(image).convert("RGB")
                                image.thumbnail((900, 900))
                                buffer = io.BytesIO()
                                image.save(buffer, format="JPEG", quality=88)
                                temporary.write_bytes(buffer.getvalue())
                        except Exception:
                            temporary.unlink(missing_ok=True)

                    ffmpeg = ffmpeg_path()
                    if (not temporary.exists() or temporary.stat().st_size == 0) and ffmpeg and is_media_path(self.path):
                        hwaccel_variants = [ffmpeg_hwaccel_args(), []]
                        if not hwaccel_variants[0]:
                            hwaccel_variants = [[]]
                        commands = [
                            [
                                ffmpeg,
                                "-y",
                                "-ss",
                                "00:00:01",
                                *hwaccel,
                                "-i",
                                str(self.path),
                                "-frames:v",
                                "1",
                                "-vf",
                                "scale=600:-1",
                                "-q:v",
                                "3",
                                str(temporary),
                            ]
                            for hwaccel in hwaccel_variants
                        ]
                        commands.extend(
                            [
                                [
                                    ffmpeg,
                                    "-y",
                                    *hwaccel,
                                    "-i",
                                    str(self.path),
                                    "-frames:v",
                                    "1",
                                    "-vf",
                                    "scale=600:-1",
                                    "-q:v",
                                    "3",
                                    str(temporary),
                                ]
                                for hwaccel in hwaccel_variants
                            ],
                        )
                        for command in commands:
                            temporary.unlink(missing_ok=True)
                            try:
                                self.run_subprocess(
                                    command,
                                    stdout=subprocess.DEVNULL,
                                    stderr=subprocess.DEVNULL,
                                    timeout=8,
                                )
                            except PreviewWorkerCancelled:
                                raise
                            except (OSError, subprocess.SubprocessError):
                                continue
                            if temporary.exists() and temporary.stat().st_size > 0:
                                break

                    if (not temporary.exists() or temporary.stat().st_size == 0) and sys.platform == "darwin":
                        try:
                            with tempfile.TemporaryDirectory() as td:
                                self.run_subprocess(
                                    ["qlmanage", "-t", "-s", "900", "-o", td, str(self.path)],
                                    stdout=subprocess.DEVNULL,
                                    stderr=subprocess.DEVNULL,
                                    timeout=8,
                                )
                                for candidate in Path(td).iterdir():
                                    if self.isInterruptionRequested():
                                        raise PreviewWorkerCancelled()
                                    if candidate.suffix.lower() in {".png", ".jpg", ".jpeg"} and candidate.stat().st_size > 0:
                                        shutil.copyfile(candidate, temporary)
                                        break
                        except PreviewWorkerCancelled:
                            raise
                        except Exception:
                            pass

                    if temporary.exists() and temporary.stat().st_size > 0:
                        # Readers see either the old complete poster or the new
                        # complete poster, never FFmpeg/Pillow's partial output.
                        os.replace(temporary, target)

                if self.isInterruptionRequested():
                    raise PreviewWorkerCancelled()
                if target.exists() and target.stat().st_size > 0:
                    try:
                        target.touch()
                    except OSError:
                        pass
                    self.loaded.emit(self.request_id, target.read_bytes())
                else:
                    self.failed.emit(self.request_id)
        except PreviewWorkerCancelled:
            raise
        except Exception:
            self.failed.emit(self.request_id)
        finally:
            if temporary is not None:
                try:
                    temporary.unlink(missing_ok=True)
                except OSError:
                    pass


class PreviewMetadataWorker(PreviewProcessWorker):
    loaded = Signal(object, object)
    failed = Signal(object)

    def __init__(self, path: Path, cache_key: Optional[Tuple[object, ...]] = None):
        super().__init__()
        self.path = path
        self.cache_key = cache_key

    def execute(self):
        try:
            meta = media_metadata(self.path, run_process=self.run_subprocess)
            if self.isInterruptionRequested():
                raise PreviewWorkerCancelled()
            self.loaded.emit(self.path, meta)
        except PreviewWorkerCancelled:
            raise
        except Exception:
            self.failed.emit(self.path)


class PreviewTextWorker(PreviewProcessWorker):
    loaded = Signal(int, object, str)
    failed = Signal(int, object)

    def __init__(self, request_id: int, path: Path, limit: int = 120_000):
        super().__init__()
        self.request_id = request_id
        self.path = path
        self.limit = max(0, int(limit))

    def execute(self):
        try:
            chunks: List[bytes] = []
            remaining = self.limit
            with self.path.open("rb") as handle:
                while remaining > 0:
                    if self.isInterruptionRequested():
                        raise PreviewWorkerCancelled()
                    chunk = handle.read(min(32_768, remaining))
                    if not chunk:
                        break
                    chunks.append(chunk)
                    remaining -= len(chunk)
            if self.isInterruptionRequested():
                raise PreviewWorkerCancelled()
            self.loaded.emit(
                self.request_id,
                self.path,
                b"".join(chunks).decode("utf-8", errors="replace"),
            )
        except PreviewWorkerCancelled:
            raise
        except Exception:
            self.failed.emit(self.request_id, self.path)


# ---------------------------------------------------------------------------
# Timeline and seek controls


def media_meta_duration_ms(meta: Optional[MediaMeta]) -> int:
    """Return one stable millisecond timeline from probed source metadata."""
    try:
        return max(
            0,
            round(float(getattr(meta, "duration_seconds", 0.0) or 0.0) * 1000.0),
        )
    except (TypeError, ValueError):
        return 0


def preview_player_duration_ms(player: object, fallback: int = 0) -> int:
    provider = getattr(player, "duration", None)
    if not callable(provider):
        return max(0, int(fallback))
    try:
        return max(0, int(provider()))
    except (AttributeError, RuntimeError, TypeError, ValueError):
        return max(0, int(fallback))


def preview_player_position_ms(player: object, fallback: int = 0) -> int:
    provider = getattr(player, "position", None)
    if not callable(provider):
        return max(0, int(fallback))
    try:
        return max(0, int(provider()))
    except (AttributeError, RuntimeError, TypeError, ValueError):
        return max(0, int(fallback))


class PreviewSeekController(QObject):
    """Own decoder seek ordering and reject stale backend position signals.

    Qt applies ``setPosition`` asynchronously.  A queued position signal from
    before the final mouse release must not drag the visible thumb back over a
    user's newer target.  The controller therefore keeps the committed target
    authoritative until the backend acknowledges it (or a bounded guard
    expires), and gives delayed proxy-rebind callbacks a revision to validate.
    """

    def __init__(
        self,
        player_provider: Callable[[], object],
        parent=None,
        interval_ms: int = 35,
        acknowledgement_tolerance_ms: int = 900,
        guard_timeout_ms: int = 3000,
    ):
        super().__init__(parent)
        self.player_provider = player_provider
        self.pending_position: Optional[int] = None
        self.committed_position: Optional[int] = None
        self.committed_reason = ""
        self.commit_revision = 0
        self.commit_started_at = 0.0
        self.commit_deadline = 0.0
        self.acknowledgement_tolerance_ms = max(0, int(acknowledgement_tolerance_ms))
        self.guard_timeout_ms = max(100, int(guard_timeout_ms))
        self._suppression_reported = False
        self.timer = QTimer(self)
        self.timer.setSingleShot(True)
        self.timer.setTimerType(Qt.PreciseTimer)
        self.timer.setInterval(max(1, int(interval_ms)))
        self.timer.timeout.connect(self.flush)
        self.guard_timer = QTimer(self)
        self.guard_timer.setSingleShot(True)
        self.guard_timer.setTimerType(Qt.PreciseTimer)
        self.guard_timer.timeout.connect(self._verify_or_expire_commit)

    def _clear_commit(self):
        self.guard_timer.stop()
        self.committed_position = None
        self.committed_reason = ""
        self.commit_started_at = 0.0
        self.commit_deadline = 0.0
        self._suppression_reported = False

    def _verify_or_expire_commit(self):
        """Bound a seek guard even when a paused backend emits no more signals."""
        target = self.committed_position
        if target is None:
            return
        now = time.monotonic()
        player = self.player_provider()
        if player is not None and now - self.commit_started_at >= 0.06:
            actual = preview_player_position_ms(player, fallback=-1)
            if actual >= 0 and abs(actual - target) <= self.acknowledgement_tolerance_ms:
                self._clear_commit()
                return
        remaining_ms = round((self.commit_deadline - now) * 1000.0)
        if remaining_ms <= 0:
            self._clear_commit()
            return
        self.guard_timer.start(max(1, remaining_ms))

    def schedule(self, position: int):
        self.pending_position = max(0, int(position))
        if not self.timer.isActive():
            self.timer.start()

    def flush(self, position: Optional[int] = None):
        if position is not None:
            self.pending_position = max(0, int(position))
        pending = self.pending_position
        self.pending_position = None
        self.timer.stop()
        if pending is None:
            return
        return self.commit(pending)

    def claim(self, position: int, *, reason: str = "user seek", timeout_ms: Optional[int] = None) -> int:
        """Make ``position`` authoritative before Qt can emit reset signals."""
        self.timer.stop()
        self.pending_position = None
        self.commit_revision += 1
        self.committed_position = max(0, int(position))
        self.committed_reason = str(reason or "seek")
        self.commit_started_at = time.monotonic()
        timeout = self.guard_timeout_ms if timeout_ms is None else max(100, int(timeout_ms))
        self.commit_deadline = self.commit_started_at + timeout / 1000.0
        self._suppression_reported = False
        self.guard_timer.start(min(80, timeout))
        return self.commit_revision

    def apply_claim(self, revision: int, position: Optional[int] = None) -> bool:
        """Apply a claimed target only if no newer user/rebind action replaced it."""
        if int(revision) != self.commit_revision:
            return False
        target = self.committed_position if position is None else max(0, int(position))
        if target is None:
            return False
        player = self.player_provider()
        if player is None:
            return False
        player.setPosition(target)
        return True

    def commit(self, position: int, *, reason: str = "user seek", timeout_ms: Optional[int] = None) -> int:
        revision = self.claim(position, reason=reason, timeout_ms=timeout_ms)
        self.apply_claim(revision)
        return revision

    def reapply_if_current(self, revision: int, position: int) -> bool:
        """Retry a post-source-load seek without overruling a newer interaction."""
        if int(revision) != self.commit_revision:
            return False
        player = self.player_provider()
        if player is None:
            return False
        player.setPosition(max(0, int(position)))
        return True

    def preferred_position(self, fallback: int = 0) -> int:
        if self.committed_position is not None and time.monotonic() >= self.commit_deadline:
            self._clear_commit()
        if self.committed_position is not None:
            return max(0, int(self.committed_position))
        return max(0, int(fallback))

    def filter_backend_position(self, position: int) -> Tuple[int, Optional[str], Optional[int]]:
        """Return the position the UI should show plus a diagnostic event.

        Events are emitted only once for suppression and once for the terminal
        acknowledgement/timeout, keeping the debugger useful without flooding
        it on every playback tick.
        """
        backend_position = max(0, int(position))
        target = self.committed_position
        if target is None:
            return backend_position, None, None

        now = time.monotonic()
        old_enough_to_acknowledge = now - self.commit_started_at >= 0.06
        if (
            old_enough_to_acknowledge
            and abs(backend_position - target) <= self.acknowledgement_tolerance_ms
        ):
            self._clear_commit()
            return backend_position, "acknowledged", target
        if now >= self.commit_deadline:
            self._clear_commit()
            return backend_position, "timed out", target
        if not self._suppression_reported:
            self._suppression_reported = True
            return target, "suppressed stale backend position", target
        return target, None, target

    def cancel(self):
        self.timer.stop()
        self.pending_position = None
        self.commit_revision += 1
        self._clear_commit()


def handle_preview_seek_mouse(owner: object, slider: QSlider, event) -> bool:
    """Make the preview timeline respond to clicks and drags anywhere."""
    event_type = event.type()
    if event_type not in (
        QEvent.MouseButtonPress,
        QEvent.MouseMove,
        QEvent.MouseButtonRelease,
    ):
        return False
    left_button = Qt.LeftButton
    if event_type == QEvent.MouseButtonPress and event.button() != left_button:
        return False
    active = bool(getattr(owner, "_preview_seek_mouse_active", False))
    if event_type == QEvent.MouseMove and not active:
        return False
    if event_type == QEvent.MouseButtonRelease and not active:
        return False
    try:
        width = max(1, slider.width() - 1)
        x = max(0.0, min(float(width), float(event.position().x())))
        minimum = int(slider.minimum())
        maximum = int(slider.maximum())
        value = minimum if maximum <= minimum else minimum + round((maximum - minimum) * x / width)
        if event_type == QEvent.MouseButtonPress:
            setattr(owner, "_preview_seek_mouse_active", True)
            slider.setFocus(Qt.MouseFocusReason)
            owner.on_scrub_pressed()
        slider.setSliderPosition(value)
        owner.on_scrub_moved(value)
        # on_scrub_moved coalesces drag samples. The release handler performs
        # the one authoritative final commit while the seek guard is still
        # active; flushing here as well caused duplicate setPosition calls and
        # exposed transient backend PausedState to the pause-overlay logic.
        if event_type == QEvent.MouseButtonRelease:
            setattr(owner, "_preview_seek_mouse_active", False)
            owner.on_scrub_released()
        event.accept()
        return True
    except (AttributeError, RuntimeError):
        setattr(owner, "_preview_seek_mouse_active", False)
        return False


# ---------------------------------------------------------------------------
# Embedded preview


class PreviewPanel(QGroupBox):
    zoomRequested = Signal(object)
    metadataLoaded = Signal(object, object)

    def __init__(self, empty_title: str = "Select a file to preview it here.", compact: bool = False):
        super().__init__("Preview")
        self.preview_surface_role = "embedded"
        self.empty_title = empty_title
        self.compact = compact
        self.current_path: Optional[Path] = None
        self.opened_at = 0.0
        self.thumbnail_request_id = 0
        self.thumbnail_workers: List[PreviewThumbnailWorker] = []
        self.playable_proxy_workers: List[PreviewPlayableProxyWorker] = []
        self.playable_proxy_request_id = 0
        self.playable_proxy_source: Optional[Path] = None
        self.playing_compatibility_proxy = False
        # True only while Qt is using (or has rejected) a growing temporary
        # transport stream whose worker will later publish the final cache.
        # Keeping this separate from ``playing_compatibility_proxy`` lets a
        # good final file recover a provisional playback failure.
        self.awaiting_final_proxy = False
        self._proxy_rebind_pending = False
        self._proxy_rebind_generation = 0
        self._provisional_resume_position_ms = 0
        self.playback_recovery_source: Optional[Path] = None
        self._debug_last_media_status = None
        self._debug_last_playback_state = None
        self._debug_last_capability_signature = None
        self._debug_last_error_signature = None
        self._debug_first_frame_key = None
        self._debug_last_ownership_violation = None
        self._debug_source_started_at = 0.0
        self._debug_media_descriptor: Dict[str, object] = {}
        self.metadata_workers: List[PreviewMetadataWorker] = []
        self.metadata_pending_keys: set = set()
        self.media_cache: Dict[Tuple[object, ...], MediaMeta] = {}
        self.media_player = None
        self.audio_output = None
        self.media_devices = None
        self.audio_monitor = None
        self.video_widget = None
        self.scrubbing_video = False
        self.scrub_was_playing = False
        self.priming_paused_frame = False
        self.preview_dimmed = False
        # This is a browsing preference, not a mirror of QMediaPlayer's
        # transient state. Quick Look temporarily pauses the embedded player,
        # but must not change whether newly selected rows autoplay.
        self.browse_playback_paused = False
        # The separate Preview window temporarily owns playback. Store the
        # owner identity so a delayed close from an older dialog cannot unlock
        # a newer one.
        self.external_playback_owner = None
        # A completed/direct same-file source can remain assigned and paused
        # while the large Preview owns playback.  Retaining it avoids a full Qt
        # decoder teardown/reparse when that window closes.
        self._external_owner_retained_transport = False
        self.global_playback_lock_owners: List[object] = []
        self.media_playback_requested = False
        self.poster_only = False
        self.media_duration_ms = 0
        self.metadata_duration_ms = 0
        self.pending_media_seek_ms: Optional[int] = None
        self.settings = app_settings()
        self.preview_muted = settings_bool(
            self.settings,
            "preview/muted",
            settings_bool(self.settings, "thumbnail_preview/muted", True),
        )
        self.thumbnail_click_timer = QTimer(self)
        self.thumbnail_click_timer.setSingleShot(True)
        self.thumbnail_click_timer.timeout.connect(self.toggle_media_playback)
        self.video_poster_timer = QTimer(self)
        self.video_poster_timer.setSingleShot(True)
        self.video_poster_timer.timeout.connect(self.start_pending_video_poster)
        self.pending_video_poster_path: Optional[Path] = None
        self.scrub_seeker = PreviewSeekController(lambda: self.media_player, self)

        # PreviewPanel uses fixed media sizes so the preview does not fight the inspector layout.
        # Important: media_height is ONLY the thumbnail/video area. The scrubber row gets its
        # own reserved strip below it, otherwise the slider overlaps the thumbnail.
        media_width = 300 if not compact else 300
        media_height = 132 if not compact else 150
        control_height = 26
        panel_padding = 8

        panel_height = media_height + control_height + panel_padding
        group_height = 196 if not compact else panel_height + 26
        self.setMinimumHeight(group_height)
        self.setMaximumHeight(group_height)

        layout = QHBoxLayout(self)
        layout.setContentsMargins(0, 2, 0, 0)
        layout.setSpacing(14 if not compact else 0)

        media_panel = QWidget()
        media_panel.setObjectName("PreviewMediaPanel")
        media_panel.setFixedSize(media_width, panel_height)
        media_panel.setStyleSheet("background: transparent;")
        media_layout = QVBoxLayout(media_panel)
        media_layout.setContentsMargins(0, 0, 0, 0)
        media_layout.setSpacing(6)

        self.preview_stack = QStackedWidget()
        self.preview_stack.setFixedSize(media_width, media_height)
        self.preview_stack.setStyleSheet(
            f"background: {PREVIEW_CANVAS_COLOR}; border: none;"
        )

        self.thumbnail_label = QLabel("No preview")
        self.thumbnail_label.setObjectName("ThumbnailPreview")
        self.thumbnail_label.setFixedSize(media_width, media_height)
        self.thumbnail_label.setAlignment(Qt.AlignCenter)
        self.thumbnail_label.setWordWrap(True)
        self.thumbnail_label.setContentsMargins(10, 6, 10, 6)
        self.thumbnail_label.setCursor(Qt.PointingHandCursor)
        self.thumbnail_label.installEventFilter(self)
        self.preview_stack.addWidget(self.thumbnail_label)

        if MEDIA_PREVIEW_AVAILABLE and QMediaPlayer and QAudioOutput and QVideoSink:
            # This surface is only 300x132. Thirty converted frames per second
            # are visually smooth here and avoid scaling 4K frames at 120 Hz.
            self.video_widget = FrameVideoWidget(target_fps=30)
            self.video_widget.setObjectName("VideoPreview")
            self.video_widget.setFixedSize(media_width, media_height)
            self.video_widget.setCursor(Qt.PointingHandCursor)
            self.video_widget.installEventFilter(self)
            self.preview_stack.addWidget(self.video_widget)
            self.audio_output = QAudioOutput(self)
            self.media_devices = follow_system_audio_output(self, self.audio_output)
            self.audio_output.setMuted(self.preview_muted)
            self.audio_output.setVolume(0.8)
            self.media_player = QMediaPlayer(self)
            self.media_player.setAudioOutput(self.audio_output)
            self.media_player.setVideoSink(self.video_widget.video_sink)
            self.audio_monitor = install_preview_audio_diagnostics(
                self,
                self.media_player,
                self.audio_output,
                "embedded",
            )
            self.video_widget.firstFrameReady.connect(self.on_video_first_frame_ready)
            self.video_widget.frameConversionUnavailable.connect(self.on_video_frame_conversion_unavailable)
            if hasattr(self.media_player, "setLoops") and hasattr(QMediaPlayer, "Loops"):
                try:
                    self.media_player.setLoops(QMediaPlayer.Loops.Infinite)
                except Exception:
                    pass
            self.media_player.durationChanged.connect(self.on_video_duration_changed)
            self.media_player.positionChanged.connect(self.on_video_position_changed)
            self.media_player.mediaStatusChanged.connect(self.on_video_media_status_changed)
            self.media_player.playbackStateChanged.connect(self.on_video_playback_state_changed)
            self.media_player.errorOccurred.connect(self.on_video_playback_error)
            for signal_name in (
                "hasVideoChanged",
                "hasAudioChanged",
                "tracksChanged",
                "seekableChanged",
                "bufferProgressChanged",
                "sourceChanged",
            ):
                signal = getattr(self.media_player, signal_name, None)
                if signal is not None:
                    signal.connect(lambda *_args: self.on_video_capabilities_changed())

        # Audio uses this child overlay. Video paints its pause state directly
        # on the retained decoded frame.
        self.paused_overlay = QLabel("-paused-", self.preview_stack)
        self.paused_overlay.setObjectName("PausedOverlay")
        self.paused_overlay.setAlignment(Qt.AlignCenter)
        self.paused_overlay.setAttribute(Qt.WA_TransparentForMouseEvents, True)
        self.paused_overlay.setAttribute(Qt.WA_StyledBackground, True)
        self.paused_overlay.setStyleSheet(PAUSED_OVERLAY_STYLE)
        self.position_paused_overlay()
        self.paused_overlay.hide()
        media_layout.addWidget(self.preview_stack)
        scrub_row = QHBoxLayout()
        scrub_row.setContentsMargins(0, 0, 0, 0)
        scrub_row.setSpacing(6)
        self.play_button = QToolButton()
        self.play_button.setObjectName("PreviewPlayButton")
        self.play_button.setFixedSize(28, 22)
        self.play_button.setText("▶")
        self.play_button.setToolTip("Play / pause")
        self.play_button.clicked.connect(self.toggle_media_playback)
        scrub_row.addWidget(self.play_button)
        self.scrub_slider = QSlider(Qt.Horizontal)
        self.scrub_slider.setObjectName("PreviewScrubSlider")
        self.scrub_slider.setFixedHeight(22)
        self.scrub_slider.setRange(0, 0)
        self.scrub_slider.setEnabled(False)
        self.scrub_slider.setTracking(True)
        self.scrub_slider.sliderPressed.connect(self.on_scrub_pressed)
        self.scrub_slider.sliderReleased.connect(self.on_scrub_released)
        self.scrub_slider.sliderMoved.connect(self.on_scrub_moved)
        self.scrub_slider.installEventFilter(self)
        scrub_row.addWidget(self.scrub_slider, stretch=1)
        self.mute_button = QToolButton()
        self.mute_button.setObjectName("PreviewMuteButton")
        self.mute_button.setFixedSize(64, 22)
        self.mute_button.clicked.connect(self.toggle_preview_mute)
        scrub_row.addWidget(self.mute_button)
        media_layout.addLayout(scrub_row)
        self.update_mute_button()
        layout.addWidget(media_panel, alignment=Qt.AlignCenter)

        info_panel = QWidget()
        self.info_panel = info_panel
        info_panel.setObjectName("PreviewInfoPanel")
        info_panel.setStyleSheet("background: transparent; border: none;")
        info_panel.setMinimumWidth(560)
        info_panel.setMaximumHeight(177)
        info_layout = QGridLayout(info_panel)
        info_layout.setContentsMargins(0, 0, 0, 0)
        info_layout.setHorizontalSpacing(14)
        info_layout.setVerticalSpacing(4)
        info_layout.setColumnMinimumWidth(0, 110)
        info_layout.setColumnMinimumWidth(1, 420)
        info_layout.setColumnStretch(1, 10)
        if not compact:
            layout.addWidget(info_panel, stretch=1, alignment=Qt.AlignTop)
        else:
            info_panel.hide()

        self.preview_title = QLabel(empty_title)
        self.preview_title.setObjectName("PreviewTitle")
        self.preview_title.setWordWrap(False)
        self.preview_title.setFixedHeight(22)
        self.preview_title.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)
        self._last_preview_title_full = empty_title

        self.preview_kind = QLabel("-")
        self.preview_duration = QLabel("-")
        self.preview_resolution = QLabel("-")
        self.preview_sample_rate = QLabel("-")
        self.preview_size = QLabel("-")
        self.preview_modified = QLabel("-")

        labels = [
            QLabel("Kind:"),
            QLabel("Duration:"),
            QLabel("Resolution:"),
            QLabel("Sample Rate:"),
            QLabel("Size:"),
            QLabel("Modified:"),
        ]
        self.preview_field_labels = labels
        self.preview_value_labels = [
            self.preview_kind,
            self.preview_duration,
            self.preview_resolution,
            self.preview_sample_rate,
            self.preview_size,
            self.preview_modified,
        ]
        for label in self.preview_field_labels + self.preview_value_labels:
            label.setMinimumHeight(19)
            label.setMaximumHeight(19)

        info_layout.addWidget(self.preview_title, 0, 0, 1, 2)
        for row, (label, value) in enumerate(zip(labels, self.preview_value_labels), start=1):
            info_layout.addWidget(label, row, 0, alignment=Qt.AlignLeft)
            info_layout.addWidget(value, row, 1, alignment=Qt.AlignLeft)

        self.reset()
        register_video_owner(self)
        self.destroyed.connect(lambda *_args: unregister_video_owner(self))
        app = QApplication.instance()
        if app is not None:
            app.aboutToQuit.connect(self.stop_preview_workers)

    def stop_preview_workers(self):
        self.cancel_video_poster_fallback(cancel_worker=True)
        self.playable_proxy_request_id += 1
        self.playable_proxy_source = None
        self.playing_compatibility_proxy = False
        self.playback_recovery_source = None
        workers = list(self.thumbnail_workers) + list(self.metadata_workers) + list(self.playable_proxy_workers)
        stop_preview_worker_collection(workers, wait_for_exit=False)
        self.thumbnail_workers.clear()
        self.metadata_workers.clear()
        self.playable_proxy_workers.clear()
        self.metadata_pending_keys.clear()

    def eventFilter(self, watched, event):
        if watched is getattr(self, "scrub_slider", None):
            if handle_preview_seek_mouse(self, self.scrub_slider, event):
                return True
        if event.type() == QEvent.MouseButtonDblClick and event.button() == Qt.LeftButton:
            if watched in (self.thumbnail_label, self.video_widget) and self.current_path:
                self.thumbnail_click_timer.stop()
                self.zoomRequested.emit(self.current_path)
                event.accept()
                return True
        if event.type() == QEvent.MouseButtonPress and event.button() == Qt.LeftButton:
            if watched in (self.thumbnail_label, self.video_widget):
                self.thumbnail_click_timer.start(QApplication.doubleClickInterval() + 20)
                event.accept()
                return True
        return super().eventFilter(watched, event)

    def reset(self):
        self.stop_video_preview()
        self.poster_only = False
        self.current_path = None
        self.set_preview_title_text(self.empty_title)
        self.set_preview_fields(
            [
                ("Kind:", "-"),
                ("Duration:", "-"),
                ("Resolution:", "-"),
                ("Sample Rate:", "-"),
                ("Size:", "-"),
                ("Modified:", "-"),
            ]
        )
        self.set_placeholder("No preview")

    def set_preview_fields(self, rows: List[Tuple[str, str]]):
        rows = rows[: len(self.preview_field_labels)]
        while len(rows) < len(self.preview_field_labels):
            rows.append(("", ""))
        for label, value, pair in zip(self.preview_field_labels, self.preview_value_labels, rows):
            label_text, value_text = pair
            label.setText(label_text)
            value.setText(value_text)
            label.setVisible(bool(label_text))
            value.setVisible(bool(label_text))

    def set_preview_title_text(self, text: str):
        full = text or self.empty_title
        self._last_preview_title_full = full
        width = max(120, self.preview_title.width() - 8)
        shown = self.preview_title.fontMetrics().elidedText(full, Qt.ElideRight, width)
        self.preview_title.setText(shown)
        self.preview_title.setToolTip(full if shown != full else "")

    def set_placeholder(self, text: str):
        self.show_thumbnail_mode()
        self.thumbnail_label.setContentsMargins(10, 6, 10, 6)
        self.thumbnail_label.setPixmap(QPixmap())
        self.thumbnail_label.setText(text)
        self.thumbnail_label.setStyleSheet(
            "border: 1px solid #4b4d55; border-radius: 6px; "
            f"background: {PREVIEW_CANVAS_COLOR}; color: #d8d9df;"
        )
        if self.logical_playback_paused():
            self.set_video_dimmed(True)

    def begin_static_poster(self, text: Optional[str] = None):
        """Leave media playback and show a web/artwork-only preview safely.

        A thumbnail can arrive after an earlier local video used the video page.
        Updating the hidden QLabel alone leaves that old surface selected; on
        macOS its native layer may also stay above later widgets. This explicit
        state transition detaches playback before a non-local poster is shown.
        """
        self.stop_video_preview()
        self.current_path = None
        self.poster_only = True
        self.show_thumbnail_mode()
        if text is not None:
            self.set_placeholder(text)
        self.set_video_dimmed(False)

    def set_static_poster_pixmap(self, pixmap: QPixmap, fallback: str = "No preview"):
        """Replace the preview with a static poster, never a hidden video page."""
        self.begin_static_poster()
        self.set_thumbnail_pixmap(pixmap, fallback=fallback)
        self.show_thumbnail_mode()
        self.set_video_dimmed(False)

    def set_thumbnail_pixmap(self, pixmap: QPixmap, fallback: str = "No preview"):
        if pixmap.isNull():
            self.set_placeholder(fallback)
            return
        # Static posters are the paused mirror of the full preview.  Fit the
        # entire frame just like the live/video surfaces do; aspect-fill made
        # the mirror appear to zoom whenever navigation changed to poster mode.
        self.thumbnail_label.setContentsMargins(0, 0, 0, 0)
        scaled = pixmap.scaled(
            self.thumbnail_label.width(),
            self.thumbnail_label.height(),
            Qt.KeepAspectRatio,
            Qt.SmoothTransformation,
        )
        self.thumbnail_label.setText("")
        self.thumbnail_label.setStyleSheet(
            "border: 1px solid #4b4d55; border-radius: 6px; "
            f"background: {PREVIEW_CANVAS_COLOR};"
        )
        self.thumbnail_label.setPixmap(scaled)
        if self.logical_playback_paused():
            self.set_video_dimmed(True)

    def apply_artwork_pixmap(self, pixmap: QPixmap, fallback: str):
        if pixmap.isNull():
            self.thumbnail_label.setContentsMargins(10, 6, 10, 6)
            self.thumbnail_label.setPixmap(QPixmap())
            self.thumbnail_label.setText(fallback)
            self.thumbnail_label.setStyleSheet(
                "border: 1px solid #4b4d55; border-radius: 6px; "
                f"background: {PREVIEW_CANVAS_COLOR}; color: #d8d9df;"
            )
            return
        self.set_thumbnail_pixmap(pixmap, fallback=fallback)

    def media_cache_key(self, path: Path) -> Optional[Tuple[object, ...]]:
        return preview_file_identity(path)

    def store_media_metadata(self, key: Tuple[object, ...], meta: MediaMeta):
        # Dict insertion order gives a compact LRU-like bound. Reinsert hits so
        # recently refreshed media is not the first entry evicted.
        self.media_cache.pop(key, None)
        self.media_cache[key] = meta
        while len(self.media_cache) > 512:
            self.media_cache.pop(next(iter(self.media_cache)))

    def cached_media_metadata_if_ready(self, path: Path) -> Optional[MediaMeta]:
        key = self.media_cache_key(path)
        if key is None:
            return None
        meta = self.media_cache.pop(key, None)
        if meta is not None:
            self.media_cache[key] = meta
        return meta

    def request_media_metadata(self, path: Path):
        key = self.media_cache_key(path)
        if key is None or key in self.media_cache or key in self.metadata_pending_keys:
            return
        self.metadata_pending_keys.add(key)
        worker = PreviewMetadataWorker(path, key)
        self.metadata_workers.append(worker)
        worker.loaded.connect(
            lambda loaded_path, meta, cache_key=key: self.on_metadata_loaded(
                loaded_path,
                meta,
                cache_key,
            )
        )
        worker.failed.connect(
            lambda failed_path, cache_key=key: self.on_metadata_failed(
                failed_path,
                cache_key,
            )
        )
        worker.finished.connect(lambda worker=worker: self.cleanup_metadata_worker(worker))
        worker.start()

    def on_metadata_loaded(
        self,
        path: Path,
        meta: MediaMeta,
        requested_key: Optional[Tuple[object, ...]] = None,
    ):
        current_key = self.media_cache_key(path)
        if requested_key is not None:
            self.metadata_pending_keys.discard(requested_key)
        # Do not associate metadata with a file that changed while ffprobe was
        # running; a later request will inspect the new contents.
        if current_key is not None and (requested_key is None or current_key == requested_key):
            self.store_media_metadata(current_key, meta)
        if self.current_path == path and (requested_key is None or current_key == requested_key):
            self.apply_metadata_to_fields(path, meta)
            self.metadataLoaded.emit(path, meta)
            preview_trace(
                "embedded",
                "metadata probe completed",
                path,
                **media_preview_descriptor(path, meta),
            )
            if (
                not self.poster_only
                and preview_requires_compatibility_proxy(path, meta)
                and not self.playing_compatibility_proxy
                and not preview_proxy_running(self.playable_proxy_workers, path)
            ):
                self.start_compatible_video_preview(
                    path,
                    autoplay=not self.logical_playback_paused(),
                )

    def on_metadata_failed(
        self,
        path: Path,
        requested_key: Optional[Tuple[object, ...]] = None,
    ):
        if requested_key is not None:
            self.metadata_pending_keys.discard(requested_key)
        if self.current_path == path:
            preview_trace(
                "embedded",
                "metadata probe failed",
                path,
                force=True,
                decision="continue with container hint and playback watchdog",
                source_kind=preview_source_kind(self),
            )

    def cleanup_metadata_worker(self, worker: PreviewMetadataWorker):
        if worker in self.metadata_workers:
            self.metadata_workers.remove(worker)
        if worker.cache_key is not None:
            self.metadata_pending_keys.discard(worker.cache_key)
        worker.deleteLater()

    def interrupt_stale_preview_workers(self, path: Path):
        for worker in list(self.metadata_workers) + list(self.thumbnail_workers) + list(self.playable_proxy_workers):
            if getattr(worker, "path", None) == path:
                continue
            try:
                if worker.isRunning():
                    worker.cancel()
            except RuntimeError:
                pass

    def apply_metadata_to_fields(self, path: Path, meta: MediaMeta):
        suffix = path.suffix.lower()
        if is_video_path(path):
            self.preview_duration.setText(meta.duration or "-")
            self.preview_resolution.setText(meta.resolution or "-")
            self.preview_sample_rate.setText(meta.sample_rate or "-")
        elif suffix in AUDIO_EXTS:
            self.preview_duration.setText(meta.duration or "-")
            self.preview_sample_rate.setText(meta.sample_rate or "-")
        elif suffix in IMAGE_EXTS:
            self.preview_resolution.setText(meta.resolution or "-")

        if is_media_path(path) and self.current_path == path:
            self.metadata_duration_ms = media_meta_duration_ms(meta)
            effective_duration = max(self.media_duration_ms, self.metadata_duration_ms)
            if effective_duration != self.media_duration_ms:
                self.media_duration_ms = effective_duration
                self.scrub_slider.setRange(0, self.media_duration_ms)

    def reset_media_timeline(self, meta: Optional[MediaMeta] = None):
        """Reset one embedded timeline before the new source starts emitting."""
        self._proxy_rebind_generation += 1
        self._proxy_rebind_pending = False
        self._provisional_resume_position_ms = 0
        self.scrub_seeker.cancel()
        self.pending_media_seek_ms = None
        self.metadata_duration_ms = media_meta_duration_ms(meta)
        self.media_duration_ms = self.metadata_duration_ms
        self.scrub_slider.setRange(0, self.media_duration_ms)
        self.scrub_slider.setValue(0)

    def media_source_ready_for_seek(self, target: Optional[int] = None) -> bool:
        """Return whether Qt can honor ``target`` without clamping a proxy seek."""
        if self.media_player is None:
            return False
        if (
            self.playable_proxy_source is not None
            and self.current_path is not None
            and self.playable_proxy_source == self.current_path
            and not self.playing_compatibility_proxy
        ):
            return False
        source_provider = getattr(self.media_player, "source", None)
        if callable(source_provider):
            try:
                source = source_provider()
                if source is None or source.isEmpty():
                    return False
            except (AttributeError, RuntimeError, TypeError):
                return False
        if target is None or int(target) <= 0:
            return True
        duration_provider = getattr(self.media_player, "duration", None)
        if not callable(duration_provider):
            return True
        try:
            available_duration = max(0, int(duration_provider()))
        except (AttributeError, RuntimeError, TypeError, ValueError):
            return False
        if available_duration <= 0:
            return False
        return not (
            self.playing_compatibility_proxy
            and int(target) > available_duration
        )

    def apply_pending_media_seek(self):
        pending = self.pending_media_seek_ms
        if pending is None or not self.media_source_ready_for_seek(pending):
            return False
        self.pending_media_seek_ms = None
        self.scrub_seeker.commit(pending, reason="deferred user seek")
        self.scrub_slider.setValue(pending)
        if (
            self.media_playback_requested
            and not self.logical_playback_paused()
            and QMediaPlayer is not None
            and self.media_player.playbackState() != QMediaPlayer.PlaybackState.PlayingState
        ):
            self.media_player.play()
        preview_trace(
            "embedded",
            "deferred user seek applied",
            self.current_path,
            force=True,
            request_id=self.playable_proxy_request_id,
            source_kind=preview_source_kind(self),
            requested_position_ms=int(pending),
            available_duration_ms=preview_player_duration_ms(
                self.media_player,
                self.media_duration_ms,
            ),
        )
        return True

    def set_path(
        self,
        path: Optional[Path],
        meta: Optional[MediaMeta] = None,
        probe_media: bool = False,
        autoplay: bool = True,
        poster_only: bool = False,
    ):
        if not path or not path.exists():
            self.reset()
            return

        if self.current_path == path and self.poster_only == poster_only:
            if meta is not None:
                self.apply_metadata_to_fields(path, meta)
            return

        self.interrupt_stale_preview_workers(path)

        autoplay = bool(autoplay and not self.browse_playback_paused)
        if autoplay:
            # If a fullscreen preview is already playing/paused on another Space, keep the
            # small inspector preview as a quiet poster. This also prevents macOS native
            # video layers from starving the thumbnail/player surface after returning to
            # the main window.
            for owner in list(VIDEO_PLAYBACK_OWNERS):
                if owner is self:
                    continue
                try:
                    if callable(getattr(owner, "isFullScreen", None)) and owner.isFullScreen() and owner.isVisible():
                        autoplay = False
                        break
                except Exception:
                    pass

        self.current_path = path
        self.poster_only = bool(poster_only)
        self.set_preview_title_text(path.name)
        self.preview_title.setToolTip(str(path))

        if path.is_dir():
            self.stop_video_preview()
            try:
                folders = len(list_child_folders(path))
                files = len(list_files(path))
                modified = date_text(path.stat().st_mtime)
            except OSError:
                folders = 0
                files = 0
                modified = "-"
            self.set_preview_fields(
                [
                    ("Kind:", "Folder"),
                    ("Folders:", f"{human_count(folders)} folder(s)"),
                    ("Files:", f"{human_count(files)} file(s)"),
                    ("Size:", "-"),
                    ("Modified:", modified),
                    ("MIME:", "inode/directory"),
                ]
            )
            self.set_placeholder("Folder")
            return

        info = file_info(path)
        kind = kind_for_path(path)
        suffix = path.suffix.lower()
        if (
            probe_media
            and (suffix in IMAGE_EXTS or is_media_path(path))
            and (meta is None or not (meta.duration or meta.resolution or meta.sample_rate))
        ):
            meta = self.cached_media_metadata_if_ready(path)
            if meta is None:
                self.request_media_metadata(path)
        meta = meta or MediaMeta()
        self.reset_media_timeline(meta)

        if suffix in IMAGE_EXTS:
            decision = "image artwork"
            source_kind = "static artwork"
        elif is_video_path(path):
            if poster_only:
                decision = "static poster while preview window owns playback"
                source_kind = "static poster"
            elif preview_requires_compatibility_proxy(path, meta):
                decision = "buffered compatibility playback required by codec policy"
                source_kind = "compatibility proxy"
            else:
                decision = "direct Qt playback with no-frame watchdog"
                source_kind = "original media"
        elif suffix in AUDIO_EXTS:
            decision = "static poster" if poster_only else "direct Qt audio playback"
            source_kind = "static poster" if poster_only else "original media"
        else:
            decision = "static file artwork"
            source_kind = "static artwork"
        self._debug_media_descriptor = media_preview_descriptor(path, meta, info)
        preview_trace(
            "embedded",
            "preview source decision",
            path,
            force=True,
            decision=decision,
            source_kind=source_kind,
            logical_paused=bool(self.browse_playback_paused or not autoplay),
            **self._debug_media_descriptor,
        )

        if suffix in IMAGE_EXTS:
            self.set_preview_fields(
                [
                    ("Kind:", kind if not info else f"{kind} / .{info.extension}"),
                    ("Dimensions:", meta.resolution or "-"),
                    ("MIME:", "-" if not info else info.mime),
                    ("Size:", "-" if not info else human_size(info.size)),
                    ("Created:", "-" if not info else date_text(info.created)),
                    ("Modified:", "-" if not info else date_text(info.modified)),
                ]
            )
            self.stop_video_preview()
            self.start_video_thumbnail(path)
        elif is_video_path(path):
            self.set_preview_fields(
                [
                    ("Kind:", kind if not info else f"{kind} / .{info.extension}"),
                    ("Duration:", meta.duration or "-"),
                    ("Resolution:", meta.resolution or "-"),
                    ("Sample Rate:", meta.sample_rate or "-"),
                    ("Size:", "-" if not info else human_size(info.size)),
                    ("Modified:", "-" if not info else date_text(info.modified)),
                ]
            )
            if poster_only:
                # The separate Preview window owns playback. The embedded inspector
                # becomes a plain static poster while that window is open: no second
                # QMediaPlayer, no compatibility-proxy timer, and no misleading
                # -paused- overlay flashing behind the Preview window as rows change.
                self.stop_video_preview()
                self.start_video_thumbnail(path)
                self.show_external_owner_mode()
            elif preview_requires_compatibility_proxy(path, meta):
                # Qt's macOS AV1/VPx path can report Playing and decode audio
                # while yielding no video frames. The compatibility worker now
                # publishes a safely buffered stream before its full cache is
                # finished, avoiding both the black surface and the old wait.
                self.start_compatible_video_preview(path, autoplay=autoplay)
            else:
                self.start_video_preview(path, autoplay=autoplay)
        elif suffix in AUDIO_EXTS:
            self.set_preview_fields(
                [
                    ("Kind:", kind if not info else f"{kind} / .{info.extension}"),
                    ("Duration:", meta.duration or "-"),
                    ("Sample Rate:", meta.sample_rate or "-"),
                    ("MIME:", "-" if not info else info.mime),
                    ("Size:", "-" if not info else human_size(info.size)),
                    ("Modified:", "-" if not info else date_text(info.modified)),
                ]
            )
            if poster_only:
                self.stop_video_preview()
                self.start_video_thumbnail(path)
                self.show_external_owner_mode()
            else:
                self.start_audio_preview(path, autoplay=autoplay)
        else:
            self.set_preview_fields(
                [
                    ("Kind:", kind if not info else f"{kind} / .{info.extension}"),
                    ("MIME:", "-" if not info else info.mime),
                    ("Size:", "-" if not info else human_size(info.size)),
                    ("Created:", "-" if not info else date_text(info.created)),
                    ("Modified:", "-" if not info else date_text(info.modified)),
                    ("Path:", str(path)),
                ]
            )
            self.stop_video_preview()
            self.start_video_thumbnail(path)

    def show_thumbnail_mode(self):
        self.preview_stack.setCurrentWidget(self.thumbnail_label)
        self.show_paused_overlay(False)
        self.set_embedded_media_controls(False, False)
        self.scrub_slider.setRange(0, 0)
        self.scrub_slider.setValue(0)

    def set_embedded_media_controls(self, visible: bool, transport_enabled: bool):
        """Keep media chrome deterministic across direct/proxy/poster pages."""
        visible = bool(visible)
        enabled = bool(
            transport_enabled
            and self.external_playback_owner is None
            and not self.global_playback_lock_owners
            and visible_large_preview_owner(excluding=self) is None
        )
        self.scrub_slider.setVisible(visible)
        self.play_button.setVisible(visible)
        self.mute_button.setVisible(visible)
        self.scrub_slider.setEnabled(enabled)
        self.play_button.setEnabled(enabled)
        # Muting is a global preference and remains useful while a proxy loads,
        # but not while a large Preview exclusively owns the audio route.
        self.mute_button.setEnabled(
            bool(visible and self.external_playback_owner is None and not self.global_playback_lock_owners)
        )

    def show_preparing_media_mode(self):
        self.preview_stack.setCurrentWidget(self.thumbnail_label)
        self.set_embedded_media_controls(True, False)
        self.apply_preview_mute()

    def show_external_owner_mode(self):
        """Show a locked, paused mirror without running a second player."""
        video_has_visual = bool(
            self.video_widget is not None
            and self.current_path is not None
            and is_video_path(self.current_path)
            and self.video_widget.has_visual()
        )
        self.preview_stack.setCurrentWidget(
            self.video_widget if video_has_visual else self.thumbnail_label
        )
        self.set_embedded_media_controls(True, False)
        self.set_video_dimmed(True)

    def show_video_mode(self):
        if self.video_widget is None:
            self.show_thumbnail_mode()
            return
        self.preview_stack.setCurrentWidget(self.video_widget)
        self.set_embedded_media_controls(True, True)
        self.apply_preview_mute()

    def show_audio_mode(self):
        self.preview_stack.setCurrentWidget(self.thumbnail_label)
        self.set_embedded_media_controls(True, True)
        self.apply_preview_mute()

    def set_embedded_player_looping(self, enabled: bool):
        """Loop finalized media, never a still-growing compatibility prefix."""
        if self.media_player is None or QMediaPlayer is None:
            return
        loops = getattr(QMediaPlayer, "Loops", None)
        setter = getattr(self.media_player, "setLoops", None)
        if loops is None or not callable(setter):
            return
        try:
            setter(loops.Infinite if enabled else loops.Once)
        except (AttributeError, RuntimeError, TypeError):
            pass

    def show_paused_overlay(self, visible: bool):
        if not hasattr(self, "paused_overlay"):
            return

        self.position_paused_overlay()
        self.paused_overlay.setVisible(bool(visible))
        if visible:
            self.paused_overlay.raise_()

    def position_paused_overlay(self):
        if not hasattr(self, "paused_overlay") or not hasattr(self, "preview_stack"):
            return
        host = self.preview_stack
        if self.paused_overlay.parent() is not host:
            was_visible = not self.paused_overlay.isHidden()
            self.paused_overlay.setParent(host)
            self.paused_overlay.setAttribute(Qt.WA_TransparentForMouseEvents, True)
            self.paused_overlay.setVisible(was_visible)
        self.paused_overlay.setGeometry(host.rect())

    def set_video_dimmed(self, dimmed: bool):
        self.preview_dimmed = bool(dimmed)
        # QMediaPlayer already freezes the exact current frame. Keep that live
        # surface selected so pausing never jumps to a differently framed poster.
        if hasattr(self, "play_button"):
            self.play_button.setText("▶" if dimmed else "⏸")
            self.play_button.setToolTip("Play" if dimmed else "Pause")
        video_is_visible = self.video_widget is not None and self.preview_stack.currentWidget() is self.video_widget
        if self.video_widget is not None:
            self.video_widget.set_paused(dimmed and video_is_visible)
        try:
            thumbnail = self.thumbnail_label.pixmap()
            thumbnail_has_visual = thumbnail is not None and not thumbnail.isNull()
        except (AttributeError, RuntimeError):
            thumbnail_has_visual = False
        thumbnail_is_visible = self.preview_stack.currentWidget() is self.thumbnail_label
        should_show = (
            dimmed
            and self.current_path is not None
            and is_media_path(self.current_path)
            and thumbnail_is_visible
            and thumbnail_has_visual
        )
        self.show_paused_overlay(should_show and not video_is_visible)

    def resizeEvent(self, event):
        super().resizeEvent(event)
        self.position_paused_overlay()

    def stop_video_preview(self):
        self.cancel_video_poster_fallback(cancel_worker=True)
        self._external_owner_retained_transport = False
        self.playable_proxy_request_id += 1
        self.playable_proxy_source = None
        self.playing_compatibility_proxy = False
        self.awaiting_final_proxy = False
        self._proxy_rebind_generation += 1
        self._proxy_rebind_pending = False
        self._provisional_resume_position_ms = 0
        self.playback_recovery_source = None
        self.scrub_seeker.cancel()
        self.pending_media_seek_ms = None
        self.scrub_was_playing = False
        self.priming_paused_frame = False
        self.media_playback_requested = False
        reset_preview_audio_monitor(self)
        if self.media_player is not None:
            try:
                self.media_player.stop()
                self.media_player.setSource(QUrl())
            except Exception:
                pass
        if self.video_widget is not None:
            self.video_widget.reset_player_output(self.media_player)
            self.video_widget.clear_frame(clear_poster=True)
        # Detach Qt from a growing .ts before cancellation lets the worker's
        # finally block unlink that temporary file without racing the decoder.
        stop_preview_worker_collection(list(self.playable_proxy_workers), wait_for_exit=False)
        self.playable_proxy_workers.clear()
        self.scrubbing_video = False
        self.set_video_dimmed(False)
        if hasattr(self, "preview_stack"):
            self.show_thumbnail_mode()

    def pause_video_preview(self):
        if self.media_player is None:
            return
        self.media_playback_requested = False
        # A frame-prime is still real PlayingState.  Ownership changes must
        # cancel it immediately instead of waiting for firstFrameReady.
        self.priming_paused_frame = False
        try:
            if self.media_player.playbackState() == QMediaPlayer.PlaybackState.PlayingState:
                self.media_player.pause()
            self.set_video_dimmed(True)
        except Exception:
            pass

    def logical_playback_paused(self) -> bool:
        """Return pause intent without trusting transient backend states."""
        return (
            self.external_playback_owner is not None
            or bool(self.global_playback_lock_owners)
            or bool(self.browse_playback_paused)
            or not bool(self.media_playback_requested)
        )

    def relay_proxy_to_paired_preview(
        self,
        source_path: Path,
        proxy_path: str,
    ) -> bool:
        """Offer an embedded proxy buffer to its exact Preview-window owner."""
        owner = self.external_playback_owner
        if owner is None or getattr(owner, "embedded_preview_panel", None) is not self:
            return False
        if self.current_path != Path(source_path):
            return False
        accept = getattr(owner, "accept_shared_compatibility_proxy", None)
        if not callable(accept):
            return False
        try:
            return bool(accept(Path(source_path), str(proxy_path)))
        except (AttributeError, RuntimeError, TypeError):
            return False

    def relay_proxy_buffer_to_paired_preview(
        self,
        source_path: Path,
        proxy_path: str,
        buffered_duration_ms: int,
    ) -> bool:
        """Forward growth notifications only to the paired Preview window."""
        owner = self.external_playback_owner
        if owner is None or getattr(owner, "embedded_preview_panel", None) is not self:
            return False
        if self.current_path != Path(source_path):
            return False
        accept = getattr(owner, "accept_shared_compatibility_proxy_buffer", None)
        if not callable(accept):
            return False
        try:
            return bool(
                accept(
                    Path(source_path),
                    str(proxy_path),
                    max(0, int(buffered_duration_ms)),
                )
            )
        except (AttributeError, RuntimeError, TypeError, ValueError):
            return False

    def relay_poster_to_paired_preview(
        self,
        source_path: Path,
        pixmap: QPixmap,
    ) -> bool:
        """Give the paired Preview an immediate visual while its proxy loads."""
        owner = self.external_playback_owner
        if owner is None or getattr(owner, "embedded_preview_panel", None) is not self:
            return False
        if self.current_path != Path(source_path) or pixmap.isNull():
            return False
        accept = getattr(owner, "accept_shared_preview_poster", None)
        if not callable(accept):
            return False
        try:
            return bool(accept(Path(source_path), pixmap))
        except (AttributeError, RuntimeError, TypeError):
            return False

    def suspend_for_large_preview(self, owner) -> None:
        """Turn this embedded surface into a static mirror while Preview owns media."""
        if owner not in self.global_playback_lock_owners:
            self.global_playback_lock_owners.append(owner)
        path = self.current_path
        if path is not None and path.exists() and is_media_path(path):
            meta = self.cached_media_metadata_if_ready(path)
            if getattr(owner, "embedded_preview_panel", None) is self:
                # Transfer transport ownership without throwing away a same-file
                # compatibility conversion. The paired Preview immediately waits
                # on that shared cache, so canceling here only made 4K WebM
                # navigation restart the most expensive work from zero.
                self.begin_external_preview(owner, path, meta=meta)
            else:
                # An unrelated scanner/Preview must not leave this transport or
                # its private progressive proxy alive behind the new owner.
                self.set_path(
                    path,
                    meta=meta,
                    probe_media=False,
                    autoplay=False,
                    poster_only=True,
                )
                self.show_external_owner_mode()
        else:
            self.pause_video_preview()

    def release_large_preview(self, owner) -> None:
        self.global_playback_lock_owners = [item for item in self.global_playback_lock_owners if item is not owner]
        if self.global_playback_lock_owners or self.external_playback_owner is not None:
            return
        if self.poster_only and self.current_path is not None and self.current_path.exists():
            path = self.current_path
            meta = self.cached_media_metadata_if_ready(path)
            self.set_path(
                path,
                meta=meta,
                probe_media=False,
                autoplay=not self.browse_playback_paused,
                poster_only=False,
            )
            return
        self.restore_browse_playback_preference()

    def begin_external_preview(
        self,
        owner,
        path: Optional[Path],
        meta: Optional[MediaMeta] = None,
    ) -> None:
        """Mirror ``path`` while a separate Preview window owns playback."""
        if (
            self.external_playback_owner is owner
            and path is not None
            and self.current_path == path
            and self.poster_only
        ):
            if meta is not None:
                self.apply_metadata_to_fields(path, meta)
            self.show_external_owner_mode()
            return
        same_path = bool(path is not None and self.current_path == Path(path))
        active_source_path: Optional[Path] = None
        if same_path and self.media_player is not None:
            try:
                source = self.media_player.source()
                source_file = str(source.toLocalFile() or "") if source is not None else ""
                candidate = Path(source_file) if source_file else None
                if candidate is not None and candidate.exists():
                    active_source_path = candidate
            except (AttributeError, RuntimeError, TypeError, ValueError):
                active_source_path = None

        # A finalized proxy or direct source is safe to leave assigned.  A
        # dot-prefixed growing proxy is not: its producer atomically renames it
        # on completion, so that transport is detached while its last frame is
        # retained as a static mirror.
        retain_transport = bool(
            same_path
            and active_source_path is not None
            and not (
                self.playing_compatibility_proxy
                and self.awaiting_final_proxy
            )
        )
        self._external_owner_retained_transport = retain_transport
        self.external_playback_owner = owner
        self.media_playback_requested = False
        preserve_same_proxy = bool(
            same_path
            and (
                preview_proxy_running(self.playable_proxy_workers, Path(path))
                or (
                    self.playing_compatibility_proxy
                    and self.playable_proxy_source == Path(path)
                )
            )
        )
        if retain_transport:
            self.cancel_video_poster_fallback(cancel_worker=True)
            self.poster_only = True
            self.priming_paused_frame = False
            try:
                self.media_player.pause()
            except (AttributeError, RuntimeError):
                pass
            self.apply_preview_mute()
            if meta is not None:
                self.apply_metadata_to_fields(Path(path), meta)
            self.show_external_owner_mode()
            if self.video_widget is not None and self.video_widget.has_visual():
                retained_visual = self.video_widget.visual_pixmap()
                QTimer.singleShot(
                    0,
                    lambda source_path=Path(path), poster=retained_visual: (
                        self.relay_poster_to_paired_preview(source_path, poster)
                    ),
                )
            elif path is not None and is_video_path(Path(path)):
                self.start_video_thumbnail_background(Path(path))
            if self.playing_compatibility_proxy and active_source_path is not None:
                QTimer.singleShot(
                    0,
                    lambda source_path=Path(path), proxy_path=str(active_source_path): (
                        self.relay_proxy_to_paired_preview(source_path, proxy_path)
                    ),
                )
            preview_trace(
                "embedded",
                "external preview ownership acquired",
                self.current_path,
                force=True,
                decision="pause and retain same-file transport/frame for instant restoration",
                **preview_surface_snapshot(self),
            )
            return
        if preserve_same_proxy:
            active_proxy_path: Optional[str] = None
            if self.playing_compatibility_proxy and self.media_player is not None:
                try:
                    active_source = self.media_player.source()
                    candidate = str(active_source.toLocalFile() or "")
                    if candidate and Path(candidate).exists():
                        active_proxy_path = candidate
                except (AttributeError, RuntimeError, TypeError):
                    active_proxy_path = None
            # The paired large Preview needs this exact conversion.  Detach the
            # embedded transport, but let its worker finish so the window can
            # reuse the shared cache instead of throwing away several seconds
            # of work and starting the same FFmpeg job again.
            self.cancel_video_poster_fallback(cancel_worker=True)
            self.poster_only = True
            self.priming_paused_frame = False
            self.playing_compatibility_proxy = False
            reset_preview_audio_monitor(self)
            if self.media_player is not None:
                try:
                    self.media_player.stop()
                    self.media_player.setSource(QUrl())
                except (AttributeError, RuntimeError):
                    pass
            if self.video_widget is not None:
                self.video_widget.reset_player_output(self.media_player)
            if meta is not None:
                self.apply_metadata_to_fields(Path(path), meta)
            self.show_external_owner_mode()
            if (
                self.video_widget is not None
                and self.video_widget.has_visual()
            ):
                retained_visual = self.video_widget.visual_pixmap()
                QTimer.singleShot(
                    0,
                    lambda source_path=Path(path), poster=retained_visual: (
                        self.relay_poster_to_paired_preview(source_path, poster)
                    ),
                )
            elif not preview_proxy_running(self.playable_proxy_workers, Path(path)):
                # The compatibility encoder may need seconds before publishing
                # its first playable prefix.  Extract one current-file poster so
                # both surfaces provide immediate visual feedback meanwhile. Do
                # not compete with an active 4K conversion for CPU and disk I/O.
                self.start_video_thumbnail_background(Path(path))
            if active_proxy_path is not None:
                # set_path() is still constructing the Preview window here.
                # Defer the transfer one event-loop turn so its timeline and
                # compatibility waiter are initialized before the source binds.
                QTimer.singleShot(
                    0,
                    lambda source_path=Path(path), proxy_path=active_proxy_path: (
                        self.relay_proxy_to_paired_preview(source_path, proxy_path)
                    ),
                )
            preview_trace(
                "embedded",
                "external preview ownership acquired",
                self.current_path,
                force=True,
                decision="embedded transport detached; in-flight proxy retained for the Preview window",
                **preview_surface_snapshot(self),
            )
            return
        self.stop_video_preview()
        self._external_owner_retained_transport = False
        if path is not None and path.exists():
            self.set_path(
                path,
                meta=meta,
                probe_media=False,
                autoplay=False,
                poster_only=True,
            )
        if self.current_path is not None and is_media_path(self.current_path):
            self.show_external_owner_mode()
        preview_trace(
            "embedded",
            "external preview ownership acquired",
            self.current_path,
            force=True,
            decision="embedded transport stopped; locked poster mirrors the Preview window",
            **preview_surface_snapshot(self),
        )

    def end_external_preview(self, owner, restore: bool = True) -> None:
        """Release Preview ownership and restore the remembered preference."""
        if self.external_playback_owner is not owner:
            return
        path = self.current_path
        meta = self.cached_media_metadata_if_ready(path) if path is not None else None
        retained_transport = bool(self._external_owner_retained_transport)
        if retained_transport:
            # Error recovery can detach a source while Preview owns playback.
            # Never take the instant-restore path unless a real local source is
            # still assigned to the retained player.
            retained_transport = False
            if self.media_player is not None:
                try:
                    retained_source = self.media_player.source()
                    retained_file = str(retained_source.toLocalFile() or "")
                    retained_transport = bool(
                        retained_file
                        and Path(retained_file).exists()
                        and not retained_source.isEmpty()
                    )
                except (AttributeError, RuntimeError, TypeError, ValueError):
                    retained_transport = False
        self._external_owner_retained_transport = False
        self.external_playback_owner = None
        if not restore:
            self.stop_video_preview()
            return
        if retained_transport and path is not None and path.exists():
            self.poster_only = False
            self.apply_preview_mute()
            self.restore_browse_playback_preference()
            preview_trace(
                "embedded",
                "external preview ownership released",
                path,
                force=True,
                decision="resume retained same-file transport without rebuilding source",
                **preview_surface_snapshot(self),
            )
            return
        if path is not None and path.exists():
            # poster_only intentionally changes here, forcing a clean source
            # assignment after the locked state cleared the embedded player.
            self.set_path(
                path,
                meta=meta,
                probe_media=False,
                autoplay=not self.browse_playback_paused,
                poster_only=False,
            )
        preview_trace(
            "embedded",
            "external preview ownership released",
            path,
            force=True,
            decision="restore remembered embedded playback preference",
            **preview_surface_snapshot(self),
        )

    def restore_browse_playback_preference(self):
        """Reapply the user's embedded autoplay choice after temporary ownership."""
        if self.external_playback_owner is not None:
            if self.media_player is not None:
                try:
                    self.media_player.pause()
                except (AttributeError, RuntimeError):
                    pass
            self.set_video_dimmed(True)
            return
        if self.media_player is None or self.current_path is None:
            return
        if not is_media_path(self.current_path):
            return
        try:
            if self.browse_playback_paused:
                self.media_playback_requested = False
                if is_video_path(self.current_path):
                    self.show_video_mode()
                else:
                    self.show_audio_mode()
                # A newly selected video may still be playing silently only to
                # obtain its first visible frame.  Let that one-frame prime
                # finish instead of pausing before the sink can paint anything.
                if not self.priming_paused_frame:
                    self.media_player.pause()
                self.set_video_dimmed(True)
                return
            # External ownership may end before the paused-frame decode (or a
            # WebM compatibility proxy) finishes.  Invalidate that old pause
            # completion before restoring Playing, otherwise firstFrameReady
            # can arrive later and undo the user's remembered preference.
            self.priming_paused_frame = False
            if not request_video_playback(self):
                self.media_playback_requested = False
                self.show_external_owner_mode()
                return
            self.media_playback_requested = True
            if is_video_path(self.current_path):
                self.show_video_mode()
            else:
                self.show_audio_mode()
            self.media_player.play()
            self.set_video_dimmed(False)
        except Exception:
            pass

    def toggle_video_playback(self) -> bool:
        return self.toggle_media_playback()

    def toggle_media_playback(self) -> bool:
        if self.media_player is None:
            return False
        if self.current_path is None or not is_media_path(self.current_path):
            return False
        if self.external_playback_owner is not None:
            # Never let an embedded click steal playback from the large window.
            preview_trace(
                "embedded",
                "playback input ignored",
                self.current_path,
                force=True,
                decision="preview window currently owns playback",
                source_kind=preview_source_kind(self),
                request_id=self.playable_proxy_request_id,
            )
            self.set_video_dimmed(True)
            return False
        try:
            # Loading and seeking can transiently report PausedState even while
            # the embedded preview is logically playing.  User input must
            # toggle the remembered intent, not that backend implementation
            # detail, or clicks during a source transition appear to do nothing.
            if not self.logical_playback_paused():
                self.priming_paused_frame = False
                self.apply_preview_mute()
                self.media_playback_requested = False
                self.media_player.pause()
                self.browse_playback_paused = True
                self.set_video_dimmed(True)
                preview_trace(
                    "embedded",
                    "user changed playback intent",
                    self.current_path,
                    force=True,
                    decision="pause",
                    source_kind=preview_source_kind(self),
                    request_id=self.playable_proxy_request_id,
                    logical_paused=True,
                )
            else:
                if not request_video_playback(self):
                    self.media_playback_requested = False
                    self.set_video_dimmed(True)
                    return False
                self.browse_playback_paused = False
                self.priming_paused_frame = False
                self.media_playback_requested = True
                if is_video_path(self.current_path):
                    self.show_video_mode()
                else:
                    self.show_audio_mode()
                self.media_player.play()
                self.set_video_dimmed(False)
                preview_trace(
                    "embedded",
                    "user changed playback intent",
                    self.current_path,
                    force=True,
                    decision="play",
                    source_kind=preview_source_kind(self),
                    request_id=self.playable_proxy_request_id,
                    logical_paused=False,
                )
            return True
        except Exception:
            return False

    def start_compatible_video_preview(self, path: Path, autoplay: bool = True):
        """Show artwork immediately while preparing a Qt-friendly video source."""
        if (
            self.external_playback_owner is not None
            or self.global_playback_lock_owners
            or visible_large_preview_owner(excluding=self) is not None
        ):
            self.media_playback_requested = False
            self.poster_only = True
            self.stop_video_preview()
            self.start_video_thumbnail(path)
            self.show_external_owner_mode()
            return
        same_proxy_playing = bool(
            self.playing_compatibility_proxy
            and self.playable_proxy_source == path
        )
        same_proxy_running = preview_proxy_running(self.playable_proxy_workers, path)
        if same_proxy_playing or same_proxy_running:
            # Ownership can be released while the same conversion is still in
            # flight.  Reassert the visible/loading state and current autoplay
            # intent instead of returning with the panel stuck as a disabled
            # external-owner placeholder.
            self.poster_only = False
            self.media_playback_requested = bool(
                autoplay and not self.browse_playback_paused
            )
            if same_proxy_playing:
                self.show_video_mode()
                self.restore_browse_playback_preference()
            else:
                self.show_preparing_media_mode()
                self.set_video_dimmed(self.logical_playback_paused())
            return
        self.cancel_video_poster_fallback(cancel_worker=True)
        preview_trace(
            "embedded",
            "compatibility proxy requested",
            path,
            force=True,
            video_codec=container_video_codec_hint(path) or "metadata",
            decision="bypass Qt decoder and prepare compatible H.264/AAC source",
            source_kind="original media pending proxy",
            logical_paused=not bool(
                autoplay
                and self.external_playback_owner is None
                and not self.browse_playback_paused
            ),
        )
        self.start_playable_proxy_preview(path, autoplay=autoplay)
        # Do not launch a second FFmpeg decoder for a poster while the
        # compatibility transcode is already decoding this (often 4K) source.
        # A real proxy frame normally arrives first; the failure path still
        # extracts artwork when it is actually needed.

    def start_playable_proxy_preview(self, path: Path, autoplay: bool = True):
        self.media_playback_requested = bool(
            autoplay
            and self.external_playback_owner is None
            and not self.browse_playback_paused
        )
        self.playable_proxy_request_id += 1
        request_id = self.playable_proxy_request_id
        self._proxy_rebind_generation += 1
        self._proxy_rebind_pending = False
        self._provisional_resume_position_ms = 0
        self.playable_proxy_source = Path(path)
        self.playing_compatibility_proxy = False
        self.awaiting_final_proxy = False
        self._debug_source_started_at = time.monotonic()
        for worker in list(self.playable_proxy_workers):
            try:
                worker.cancel()
            except RuntimeError:
                pass
        self.priming_paused_frame = False
        if self.media_player is not None:
            try:
                self.media_player.stop()
                self.media_player.setSource(QUrl())
            except (AttributeError, RuntimeError):
                pass
        if self.video_widget is not None:
            # Never let a prior row's retained frame masquerade as the new
            # conversion while the thumbnail/proxy workers are still loading.
            self.video_widget.clear_frame(clear_poster=True)
        # Proxy preparation has no active QMediaPlayer source. Clear the old
        # source's decoded-audio counters and its pending health timer now,
        # rather than waiting until the proxy becomes ready.
        reset_preview_audio_monitor(self)
        self.set_placeholder("Preparing compatible video preview…")
        self.show_preparing_media_mode()
        preview_trace(
            "embedded",
            "proxy worker started",
            path,
            force=True,
            request_id=request_id,
            source_kind="proxy worker",
            decision="background conversion or cache validation",
            logical_paused=bool(self.logical_playback_paused()),
        )
        worker = PreviewPlayableProxyWorker(request_id, path, surface="embedded")
        self.playable_proxy_workers.append(worker)
        worker.ready.connect(lambda rid, proxy, a=autoplay: self.on_playable_proxy_ready(rid, proxy, a))
        worker.bufferExtended.connect(self.on_playable_proxy_buffer_extended)
        worker.finalized.connect(self.on_playable_proxy_finalized)
        worker.failed.connect(self.on_playable_proxy_failed)
        worker.progress.connect(self.on_playable_proxy_progress)
        worker.finished.connect(lambda w=worker: self.cleanup_playable_proxy_worker(w))
        worker.start()

    def on_playable_proxy_progress(self, request_id: int, message: str):
        if request_id != self.playable_proxy_request_id:
            return
        if self.current_path != self.playable_proxy_source:
            return
        try:
            poster = self.thumbnail_label.pixmap()
            has_poster = poster is not None and not poster.isNull()
        except (AttributeError, RuntimeError):
            has_poster = False
        if has_poster:
            self.thumbnail_label.setToolTip(message)
        else:
            self.set_placeholder(message)
        self.show_preparing_media_mode()
        preview_trace(
            "embedded",
            "proxy preparation progress",
            self.current_path,
            request_id=request_id,
            source_kind="proxy worker",
            decision=message,
            has_poster=has_poster,
        )

    def on_playable_proxy_ready(self, request_id: int, proxy_path: str, autoplay: bool):
        if request_id != self.playable_proxy_request_id or self.current_path != self.playable_proxy_source:
            return
        self.awaiting_final_proxy = Path(proxy_path).name.startswith(".")
        proxy_source_kind = (
            "growing compatibility proxy"
            if self.awaiting_final_proxy
            else "validated compatibility proxy"
        )
        playback_locked = bool(
            self.external_playback_owner is not None
            or self.global_playback_lock_owners
            or visible_large_preview_owner(excluding=self) is not None
        )
        relayed_to_preview = bool(
            playback_locked
            and self.playable_proxy_source is not None
            and self.relay_proxy_to_paired_preview(
                self.playable_proxy_source,
                proxy_path,
            )
        )
        if self.media_player is None or self.video_widget is None:
            return
        if playback_locked:
            # A worker can finish after the large Preview acquired ownership.
            # Never bind or prime that stale proxy in the embedded player. The
            # exact paired Preview can consume the same progressive file now;
            # unrelated scanner windows still receive only a static mirror.
            self.media_playback_requested = False
            self.playing_compatibility_proxy = False
            self.poster_only = True
            reset_preview_audio_monitor(self)
            try:
                self.media_player.stop()
                self.media_player.setSource(QUrl())
            except (AttributeError, RuntimeError):
                pass
            self.video_widget.reset_player_output(self.media_player)
            self.show_external_owner_mode()
            preview_trace(
                "embedded",
                "proxy ready while embedded playback was locked",
                self.current_path,
                force=True,
                request_id=request_id,
                source_kind=proxy_source_kind,
                decision=(
                    "relay buffered source to paired Preview; retain static mirror"
                    if relayed_to_preview
                    else "discard playback handoff; retain static mirror"
                ),
                **preview_surface_snapshot(self),
            )
            return
        # Keep the FFmpeg poster visible until the first proxy frame arrives.
        self.video_widget.clear_frame(clear_poster=False)
        self.show_video_mode()
        self.playback_recovery_source = None
        self.media_player.stop()
        self.video_widget.reset_player_output(self.media_player)
        self.playing_compatibility_proxy = True
        self._proxy_rebind_pending = False
        reset_preview_audio_monitor(self)
        self.media_player.setSource(QUrl.fromLocalFile(proxy_path))
        self.set_embedded_player_looping(not self.awaiting_final_proxy)
        preview_trace(
            "embedded",
            "Qt playback source assigned",
            self.current_path,
            force=True,
            request_id=request_id,
            source_kind=proxy_source_kind,
            decision="proxy ready; bind to QMediaPlayer/QVideoSink",
            elapsed_ms=round((time.monotonic() - self._debug_source_started_at) * 1000),
        )
        self.scrub_slider.setRange(0, self.media_duration_ms)
        self.scrub_slider.setValue(0)
        self.apply_preview_mute()
        # ``autoplay`` describes the state when conversion started. Ownership
        # or a user click may have changed while FFmpeg was running, so current
        # logical intent is authoritative when the proxy finally becomes ready.
        autoplay = bool(
            self.media_playback_requested
            and self.external_playback_owner is None
            and not self.browse_playback_paused
        )
        self.media_playback_requested = autoplay
        if autoplay:
            if request_video_playback(self):
                self.media_player.play()
                self.set_video_dimmed(False)
            else:
                self.media_playback_requested = False
                self.show_external_owner_mode()
        else:
            self.prime_current_paused_video_frame()
        self.schedule_video_poster_fallback(self.current_path, delay_ms=5000)
        preview_trace(
            "embedded",
            "proxy playback requested",
            self.current_path,
            force=True,
            request_id=request_id,
            source_kind=proxy_source_kind,
            decision="play" if autoplay else "decode one frame then remain paused",
            logical_paused=not autoplay,
        )

    def _rebind_playable_proxy_source(
        self,
        request_id: int,
        proxy_path: str,
        *,
        decision: str,
        force: bool = False,
    ):
        if (
            request_id != self.playable_proxy_request_id
            or self.current_path != self.playable_proxy_source
            or not self.playing_compatibility_proxy
            or self.media_player is None
            or self.video_widget is None
        ):
            return
        if (
            self.external_playback_owner is not None
            or self.global_playback_lock_owners
            or visible_large_preview_owner(excluding=self) is not None
        ):
            return
        if bool(getattr(self, "_proxy_rebind_pending", False)) and not force:
            return
        self._proxy_rebind_pending = True
        self._proxy_rebind_generation += 1
        rebind_generation = self._proxy_rebind_generation
        backend_position = max(0, int(self.media_player.position()))
        pending_position = self.pending_media_seek_ms
        resume_position = max(
            backend_position,
            max(0, int(self._provisional_resume_position_ms)),
        )
        position = max(
            0,
            int(
                pending_position
                if pending_position is not None
                else self.scrub_seeker.preferred_position(resume_position)
            ),
        )
        seek_revision = None
        if pending_position is None:
            seek_revision = self.scrub_seeker.claim(
                position,
                reason="compatibility proxy rebind",
                timeout_ms=5000,
            )
        autoplay = bool(
            pending_position is None
            and
            self.media_playback_requested
            and not self.browse_playback_paused
            and request_video_playback(self)
        )
        # Keep the last buffered frame painted while QMediaPlayer reopens the
        # finalized file; source rebinding must not flash black.
        self.media_player.stop()
        self.media_player.setSource(QUrl())
        self.video_widget.reset_player_output(self.media_player)
        reset_preview_audio_monitor(self)
        self.media_player.setSource(QUrl.fromLocalFile(proxy_path))
        self.set_embedded_player_looping(not Path(proxy_path).name.startswith("."))
        if seek_revision is not None:
            self.scrub_seeker.apply_claim(seek_revision, position)
        self.apply_preview_mute()
        if pending_position is not None:
            self.scrub_slider.setValue(position)
            self.apply_pending_media_seek()
        elif autoplay:
            self.media_player.play()
            self.set_video_dimmed(False)
        else:
            self.prime_current_paused_video_frame()
        if not Path(proxy_path).name.startswith("."):
            self._provisional_resume_position_ms = 0
        QTimer.singleShot(
            80,
            lambda rid=request_id, generation=rebind_generation, revision=seek_revision, pos=position: self.scrub_seeker.reapply_if_current(revision, pos)
            if revision is not None
            and rid == self.playable_proxy_request_id
            and generation == self._proxy_rebind_generation
            and self.current_path == self.playable_proxy_source
            and self.media_player is not None
            else None,
        )
        QTimer.singleShot(
            350,
            lambda rid=request_id, generation=rebind_generation: setattr(self, "_proxy_rebind_pending", False)
            if rid == self.playable_proxy_request_id
            and generation == self._proxy_rebind_generation
            else None,
        )
        preview_trace(
            "embedded",
            "buffered proxy source rebound",
            self.current_path,
            force=True,
            request_id=request_id,
            source_kind=(
                "growing compatibility proxy"
                if Path(proxy_path).name.startswith(".")
                else "validated compatibility proxy"
            ),
            decision=decision,
            position_ms=position,
            logical_paused=not autoplay,
        )

    def on_playable_proxy_buffer_extended(
        self,
        request_id: int,
        proxy_path: str,
        buffered_duration_ms: int,
    ):
        if (
            request_id == self.playable_proxy_request_id
            and self.current_path == self.playable_proxy_source
            and self.playable_proxy_source is not None
            and self.relay_proxy_buffer_to_paired_preview(
                self.playable_proxy_source,
                proxy_path,
                buffered_duration_ms,
            )
        ):
            return
        if (
            request_id != self.playable_proxy_request_id
            or self.current_path != self.playable_proxy_source
            or not self.playing_compatibility_proxy
            or self.media_player is None
        ):
            return
        known_duration = max(0, int(self.media_player.duration()))
        position = max(0, int(self.media_player.position()))
        pending_position = self.pending_media_seek_ms
        if pending_position is not None:
            if buffered_duration_ms < pending_position:
                return
            should_rebind = True
        else:
            if known_duration <= 0 or buffered_duration_ms <= known_duration + 3000:
                return
            if self.logical_playback_paused():
                # A paused prefix does not approach its buffered edge. Rebinding
                # it every few seconds reparses the stream and makes the UI lag;
                # the finalized callback will perform the one necessary swap.
                return
            should_rebind = known_duration - position <= 5000
        if should_rebind:
            self._rebind_playable_proxy_source(
                request_id,
                proxy_path,
                decision="refresh growing stream duration before playhead reaches buffered edge",
            )

    def on_playable_proxy_finalized(self, request_id: int, proxy_path: str):
        """Move a growing proxy session onto its completed, seekable cache."""
        if request_id != self.playable_proxy_request_id or self.current_path != self.playable_proxy_source:
            return
        if (
            self.awaiting_final_proxy
            and not self.playing_compatibility_proxy
        ):
            # Qt may reject a still-growing MPEG-TS even though the completed
            # cache is healthy.  Treat finalization as a fresh ready source
            # instead of leaving the current row on a poster forever.
            self.awaiting_final_proxy = False
            self.on_playable_proxy_ready(
                request_id,
                proxy_path,
                autoplay=not self.logical_playback_paused(),
            )
            return
        self.awaiting_final_proxy = False
        self._rebind_playable_proxy_source(
            request_id,
            proxy_path,
            decision="preserve position and playback intent on finalized cache",
            force=True,
        )

    def on_playable_proxy_failed(self, request_id: int):
        if request_id != self.playable_proxy_request_id or self.current_path != self.playable_proxy_source:
            return
        preview_trace(
            "embedded",
            "compatibility proxy failed",
            self.current_path,
            force=True,
            request_id=request_id,
            source_kind="proxy worker",
            decision="show extracted poster; see media-proxy failure",
        )
        self.playing_compatibility_proxy = False
        self.awaiting_final_proxy = False
        if self.media_player is not None:
            try:
                self.media_player.stop()
                self.media_player.setSource(QUrl())
            except (AttributeError, RuntimeError):
                pass
        reset_preview_audio_monitor(self)
        if self.current_path is not None:
            self.start_video_thumbnail_background(self.current_path)
            self.show_preparing_media_mode()

    def cleanup_playable_proxy_worker(self, worker):
        if worker in self.playable_proxy_workers:
            self.playable_proxy_workers.remove(worker)
        worker.deleteLater()

    def start_video_preview(self, path: Path, autoplay: bool = True):
        if self.media_player is None or self.video_widget is None:
            self.start_video_thumbnail(path)
            return
        if (
            self.external_playback_owner is not None
            or self.global_playback_lock_owners
            or visible_large_preview_owner(excluding=self) is not None
        ):
            self.media_playback_requested = False
            self.poster_only = True
            self.stop_video_preview()
            self.start_video_thumbnail(path)
            self.show_external_owner_mode()
            return
        if not autoplay:
            self.set_placeholder("Loading preview")
        self._proxy_rebind_generation += 1
        self._proxy_rebind_pending = False
        self._provisional_resume_position_ms = 0
        self.video_widget.clear_frame(clear_poster=True)
        self._debug_source_started_at = time.monotonic()
        self.media_playback_requested = bool(autoplay)
        self.show_video_mode()
        self.scrub_slider.setRange(0, self.media_duration_ms)
        self.scrub_slider.setValue(0)
        try:
            if autoplay and not request_video_playback(self):
                autoplay = False
                self.media_playback_requested = False
            self.playback_recovery_source = None
            self.media_player.stop()
            # Keep every video on the same QVideoSink -> FrameVideoWidget path.
            # This preserves the retained paused frame and the centered -paused- badge.
            # On macOS we disable broken hardware-decoder selection above, so AV1/VP9
            # can fall back to Qt/FFmpeg software decoding instead of a black native layer.
            self.video_widget.reset_player_output(self.media_player)
            self.playing_compatibility_proxy = False
            self.awaiting_final_proxy = False
            self.set_embedded_player_looping(True)
            self.playback_recovery_source = Path(path)
            reset_preview_audio_monitor(self)
            self.media_player.setSource(QUrl.fromLocalFile(str(path)))
            preview_trace(
                "embedded",
                "Qt playback source assigned",
                path,
                force=True,
                request_id=self.playable_proxy_request_id,
                source_kind="original media",
                decision="direct QMediaPlayer/QVideoSink playback",
                logical_paused=not autoplay,
            )
            self.apply_preview_mute()
            if autoplay:
                self.media_player.play()
                self.set_video_dimmed(False)
            else:
                self.prime_current_paused_video_frame()
            # A source opened directly in PausedState may not emit any sink
            # frame (notably WebM/VP9). Promptly bind the silent native surface
            # for that case; playing sources retain the longer slow-start grace.
            fallback_delay = preview_direct_watchdog_delay_ms(
                path,
                autoplay=autoplay,
            )
            self.schedule_video_poster_fallback(path, fallback_delay)
        except Exception as exc:
            preview_trace(
                "embedded",
                "direct playback setup failed",
                path,
                force=True,
                request_id=self.playable_proxy_request_id,
                source_kind="original media",
                decision="show thumbnail",
                error=type(exc).__name__,
            )
            self.show_thumbnail_mode()
            self.start_video_thumbnail(path)

    def on_video_playback_error(self, error, detail: str = ""):
        path = self.current_path
        backend_message = _clean_process_diagnostic(
            detail or (self.media_player.errorString() if self.media_player else ""),
            path,
            limit=900,
        )
        error_name = qt_enum_name(error)
        error_signature = (
            preview_item_id(path),
            self.playable_proxy_request_id,
            preview_source_kind(self),
            error_name,
            backend_message,
        )
        if self._debug_last_error_signature != error_signature:
            self._debug_last_error_signature = error_signature
            preview_trace(
                "embedded",
                "Qt playback error",
                path,
                force=True,
                request_id=self.playable_proxy_request_id,
                source_kind=preview_source_kind(self),
                error=error_name,
                error_code=str(error),
                backend_message=backend_message,
                **qmedia_player_snapshot(self.media_player),
            )
        if path is None or not is_video_path(path):
            return
        if self.playing_compatibility_proxy:
            QTimer.singleShot(
                0,
                lambda failed_path=Path(path): self.fallback_from_unpaintable_proxy(
                    failed_path,
                    "Qt rejected the compatibility proxy",
                ),
            )
            return
        if self.playback_recovery_source != path:
            return
        if preview_proxy_running(self.playable_proxy_workers, path):
            return
        # Error signals can arrive inside QMediaPlayer's source transition.
        # Recover on the next event-loop turn rather than mutating that source
        # from inside Qt Multimedia's callback.
        self.playback_recovery_source = None
        QTimer.singleShot(0, lambda failed_path=path: self.recover_video_playback(failed_path))

    def recover_video_playback(self, failed_path: Path):
        if self.current_path != failed_path or self.playing_compatibility_proxy:
            return
        self.start_compatible_video_preview(
            failed_path,
            autoplay=not self.logical_playback_paused(),
        )

    def fallback_from_unpaintable_proxy(self, path: Path, reason: str):
        """Never leave a permanent black page after proxy playback fails."""
        if self.current_path != path or not self.playing_compatibility_proxy:
            return
        preview_trace(
            "embedded",
            "compatibility proxy produced no paintable frame",
            path,
            force=True,
            request_id=self.playable_proxy_request_id,
            source_kind=preview_source_kind(self),
            decision="stop Qt playback and show extracted poster",
                backend_message=_clean_process_diagnostic(reason, path, limit=500),
                **video_frame_snapshot(self.video_widget),
                **qmedia_player_snapshot(self.media_player),
        )
        self.cancel_video_poster_fallback(cancel_worker=True)
        self.playing_compatibility_proxy = False
        self.playback_recovery_source = None
        if self.media_player is not None:
            try:
                self.media_player.stop()
                self.media_player.setSource(QUrl())
            except (AttributeError, RuntimeError):
                pass
        self.show_thumbnail_mode()
        self.start_video_thumbnail_background(path)
        self.show_preparing_media_mode()
        self.set_video_dimmed(self.logical_playback_paused())

    def start_audio_preview(self, path: Path, autoplay: bool = True):
        if (
            self.external_playback_owner is not None
            or self.global_playback_lock_owners
            or visible_large_preview_owner(excluding=self) is not None
        ):
            self.media_playback_requested = False
            self.poster_only = True
            self.stop_video_preview()
            self.start_video_thumbnail(path)
            self.show_external_owner_mode()
            return
        self.start_video_thumbnail(path)

        if self.media_player is None:
            return

        self._proxy_rebind_generation += 1
        self._proxy_rebind_pending = False
        self._provisional_resume_position_ms = 0
        self.media_playback_requested = bool(autoplay)

        self.show_audio_mode()
        self.scrub_slider.setRange(0, self.media_duration_ms)
        self.scrub_slider.setValue(0)
        try:
            if autoplay and not request_video_playback(self):
                autoplay = False
                self.media_playback_requested = False
            self.playback_recovery_source = None
            self.media_player.stop()
            self.set_embedded_player_looping(True)
            reset_preview_audio_monitor(self)
            self.media_player.setSource(QUrl.fromLocalFile(str(path)))
            self._debug_source_started_at = time.monotonic()
            preview_trace(
                "embedded",
                "Qt playback source assigned",
                path,
                force=True,
                request_id=self.playable_proxy_request_id,
                source_kind="original audio",
                decision="direct audio playback",
                logical_paused=not autoplay,
            )
            self.apply_preview_mute()
            if autoplay:
                self.media_player.play()
                self.set_video_dimmed(False)
            else:
                self.media_player.pause()
                self.set_video_dimmed(True)
        except Exception:
            self.set_video_dimmed(False)

    def apply_preview_mute(self):
        sync_output = getattr(self, "_sync_default_audio_output", None)
        if callable(sync_output):
            sync_output()
        if self.audio_output is not None:
            ownership_locked = bool(
                self.external_playback_owner is not None or self.global_playback_lock_owners
            )
            self.audio_output.setMuted(self.preview_muted or ownership_locked)
            self.audio_output.setVolume(0.0 if (self.preview_muted or ownership_locked) else 0.8)
        self.update_mute_button()

    def toggle_preview_mute(self):
        preview_trace(
            "embedded",
            "sound control activated",
            self.current_path,
            force=True,
            decision="unmute" if self.preview_muted else "mute",
            **audio_output_snapshot(self.audio_output),
        )
        self.preview_muted = not self.preview_muted
        self.settings.setValue("preview/muted", self.preview_muted)
        self.apply_preview_mute()
        self.sync_other_preview_mutes()
        preview_trace(
            "embedded",
            "sound control applied",
            self.current_path,
            force=True,
            **preview_surface_snapshot(self),
        )

    def set_preview_muted(self, muted: bool):
        self.preview_muted = muted
        self.apply_preview_mute()

    def sync_other_preview_mutes(self):
        for owner in list(VIDEO_PLAYBACK_OWNERS):
            if owner is self:
                continue
            setter = getattr(owner, "set_preview_muted", None)
            if callable(setter):
                setter(self.preview_muted)

    def update_mute_button(self):
        if not hasattr(self, "mute_button"):
            return
        self.mute_button.setText("Muted" if self.preview_muted else "Sound")
        self.mute_button.setToolTip("Muted. Click to enable preview sound." if self.preview_muted else "Sound on. Click to mute previews.")

    def on_video_duration_changed(self, duration: int):
        backend_duration = max(0, int(duration))
        previous_duration = self.media_duration_ms
        self.media_duration_ms = max(
            self.media_duration_ms,
            backend_duration,
            self.metadata_duration_ms,
        )
        self.scrub_slider.setRange(0, self.media_duration_ms)
        if self.media_duration_ms and self.preview_duration.text() in {"", "-"}:
            self.preview_duration.setText(format_duration(self.media_duration_ms / 1000.0) or "-")
        if self.media_duration_ms != previous_duration:
            preview_trace(
                "embedded",
                "preview timeline duration updated",
                self.current_path,
                request_id=self.playable_proxy_request_id,
                source_kind=preview_source_kind(self),
                backend_duration_ms=backend_duration,
                metadata_duration_ms=self.metadata_duration_ms,
                effective_duration_ms=self.media_duration_ms,
                provisional_proxy=bool(self.awaiting_final_proxy),
            )
        self.apply_pending_media_seek()

    def on_video_position_changed(self, position: int):
        if self.scrubbing_video or self.pending_media_seek_ms is not None:
            return
        reason = self.scrub_seeker.committed_reason
        visible_position, event, target = self.scrub_seeker.filter_backend_position(position)
        if self._proxy_rebind_pending and target is None:
            return
        if self.playing_compatibility_proxy and self.awaiting_final_proxy:
            if visible_position <= 0 and self._provisional_resume_position_ms > 0:
                visible_position = self._provisional_resume_position_ms
            elif visible_position > 0:
                self._provisional_resume_position_ms = visible_position
        self.scrub_slider.setValue(visible_position)
        if event:
            preview_trace(
                "embedded",
                f"seek backend {event}",
                self.current_path,
                force=True,
                request_id=self.playable_proxy_request_id,
                source_kind=preview_source_kind(self),
                requested_position_ms=target,
                backend_position_ms=max(0, int(position)),
                visible_position_ms=visible_position,
                available_duration_ms=(
                    preview_player_duration_ms(self.media_player, self.media_duration_ms)
                    if self.media_player is not None
                    else 0
                ),
                seek_reason=reason,
                rebind_pending=bool(self._proxy_rebind_pending),
            )

    def on_video_media_status_changed(self, status):
        if self.media_player is None:
            return
        status_name = qt_enum_name(status)
        transition_key = (
            preview_item_id(self.current_path),
            self.playable_proxy_request_id,
            preview_source_kind(self),
            status_name,
        )
        if self._debug_last_media_status != transition_key:
            self._debug_last_media_status = transition_key
            preview_trace(
                "embedded",
                "Qt media status changed",
                self.current_path,
                request_id=self.playable_proxy_request_id,
                source_kind=preview_source_kind(self),
                status=status_name,
                media_status=status_name,
                logical_paused=bool(self.logical_playback_paused()),
                **qmedia_player_snapshot(self.media_player),
            )
        if QMediaPlayer and status == QMediaPlayer.MediaStatus.EndOfMedia:
            if self.playing_compatibility_proxy and self.awaiting_final_proxy:
                available_duration = preview_player_duration_ms(
                    self.media_player,
                    self.media_duration_ms,
                )
                edge_position = max(
                    self._provisional_resume_position_ms,
                    max(0, int(self.scrub_slider.value())),
                    preview_player_position_ms(self.media_player),
                )
                if available_duration > 0:
                    edge_position = min(edge_position, available_duration)
                self._provisional_resume_position_ms = edge_position
                if self.pending_media_seek_ms is None:
                    self.scrub_slider.setValue(edge_position)
                preview_trace(
                    "embedded",
                    "provisional proxy reached buffered edge",
                    self.current_path,
                    force=True,
                    request_id=self.playable_proxy_request_id,
                    source_kind=preview_source_kind(self),
                    decision="hold current position until proxy buffer grows; do not loop to zero",
                    backend_position_ms=preview_player_position_ms(self.media_player),
                    retained_position_ms=edge_position,
                    available_duration_ms=available_duration,
                )
                return
            try:
                self.media_player.setPosition(0)
                if self.logical_playback_paused():
                    self.media_player.pause()
                    self.set_video_dimmed(True)
                else:
                    self.media_player.play()
            except Exception:
                pass

    def on_video_playback_state_changed(self, state):
        state_name = qt_enum_name(state)
        transition_key = (
            preview_item_id(self.current_path),
            self.playable_proxy_request_id,
            preview_source_kind(self),
            state_name,
        )
        if self._debug_last_playback_state != transition_key:
            self._debug_last_playback_state = transition_key
            preview_trace(
                "embedded",
                "Qt playback state changed",
                self.current_path,
                request_id=self.playable_proxy_request_id,
                source_kind=preview_source_kind(self),
                state=state_name,
                playback_state=state_name,
                logical_paused=bool(self.logical_playback_paused()),
                **qmedia_player_snapshot(self.media_player),
            )
        playback_locked = bool(
            self.external_playback_owner is not None
            or self.global_playback_lock_owners
            or visible_large_preview_owner(excluding=self) is not None
        )
        if playback_locked:
            if QMediaPlayer and state == QMediaPlayer.PlaybackState.PlayingState:
                violation = (
                    preview_item_id(self.current_path),
                    self.playable_proxy_request_id,
                    preview_source_kind(self),
                )
                if violation != self._debug_last_ownership_violation:
                    self._debug_last_ownership_violation = violation
                    preview_trace(
                        "embedded",
                        "playback ownership invariant corrected",
                        self.current_path,
                        force=True,
                        decision="embedded player entered PlayingState while a Preview window owned playback; pause immediately",
                        **preview_surface_snapshot(self),
                    )
                self.priming_paused_frame = False
                QTimer.singleShot(0, self.pause_video_preview)
            self.set_video_dimmed(True)
        elif self.scrubbing_video and self.scrub_was_playing:
            # Some Qt/codec paths briefly report PausedState for setPosition.
            # Seeking must not flash the pause badge or change user intent.
            return
        elif self.logical_playback_paused():
            self.set_video_dimmed(True)
        elif self.current_path and is_media_path(self.current_path):
            # Loading, rebinding, and seeking can briefly report PausedState.
            # The badge reflects user intent, not those backend transitions.
            self.set_video_dimmed(False)

    def on_video_capabilities_changed(self):
        ensure_active_preview_audio_track(self, "embedded")
        snapshot = qmedia_player_snapshot(self.media_player)
        signature = (
            preview_item_id(self.current_path),
            self.playable_proxy_request_id,
            preview_source_kind(self),
            snapshot.get("has_video"),
            snapshot.get("has_audio"),
            snapshot.get("player_seekable"),
            snapshot.get("duration_ms"),
        )
        if signature == self._debug_last_capability_signature:
            return
        self._debug_last_capability_signature = signature
        preview_trace(
            "embedded",
            "Qt media capabilities changed",
            self.current_path,
            request_id=self.playable_proxy_request_id,
            source_kind=preview_source_kind(self),
            logical_paused=bool(self.logical_playback_paused()),
            **snapshot,
        )

    def on_scrub_pressed(self):
        self.scrub_seeker.cancel()
        self.pending_media_seek_ms = None
        self.scrubbing_video = True
        self.scrub_was_playing = False
        if self.media_player is not None and QMediaPlayer is not None:
            try:
                self.scrub_was_playing = (
                    self.media_player.playbackState()
                    == QMediaPlayer.PlaybackState.PlayingState
                )
            except (AttributeError, RuntimeError):
                pass

    def on_scrub_released(self):
        seek_position = self.scrub_slider.value()
        try:
            # Keep scrubbing_video true through the final setPosition and any
            # synchronous Qt state signals it emits. Slider transport is not a
            # user pause and must never toggle or flash the pause presentation.
            available_duration = preview_player_duration_ms(
                self.media_player,
                self.media_duration_ms,
            )
            seek_applied = self.media_source_ready_for_seek(seek_position)
            if seek_applied:
                self.scrub_seeker.commit(seek_position, reason="user slider seek")
                self.pending_media_seek_ms = None
                if self.awaiting_final_proxy:
                    self._provisional_resume_position_ms = max(0, int(seek_position))
            else:
                self.scrub_seeker.cancel()
                self.pending_media_seek_ms = max(0, int(seek_position))
                if self.scrub_was_playing and self.media_player is not None:
                    self.media_player.pause()
            preview_trace(
                "embedded",
                "user seek committed" if seek_applied else "user seek deferred",
                self.current_path,
                force=True,
                request_id=self.playable_proxy_request_id,
                source_kind=preview_source_kind(self),
                requested_position_ms=int(seek_position),
                available_duration_ms=available_duration,
                actual_position_ms=(
                    preview_player_position_ms(self.media_player)
                    if self.media_player is not None
                    else 0
                ),
                decision=(
                    "send one authoritative decoder seek"
                    if seek_applied
                    else "keep requested thumb position until progressive source can honor it"
                ),
                logical_paused=bool(self.logical_playback_paused()),
            )
            if seek_applied and self.scrub_was_playing and self.media_player is not None and QMediaPlayer is not None:
                if (
                    self.media_player.playbackState()
                    != QMediaPlayer.PlaybackState.PlayingState
                ):
                    self.media_player.play()
        except (AttributeError, RuntimeError):
            pass
        finally:
            self.scrubbing_video = False
            self.scrub_was_playing = False

    def on_scrub_moved(self, position: int):
        # The thumb is the only thing that moves during a drag. Qt decoder
        # seeks are asynchronous and can complete out of order, so release is
        # the one authoritative transport commit.
        if self.scrubbing_video:
            return
        if self.media_source_ready_for_seek(position):
            self.pending_media_seek_ms = None
            self.scrub_seeker.commit(position, reason="slider keyboard seek")
            if self.awaiting_final_proxy:
                self._provisional_resume_position_ms = max(0, int(position))
        else:
            self.scrub_seeker.cancel()
            self.pending_media_seek_ms = max(0, int(position))

    def start_video_thumbnail_background(self, path: Path):
        self.interrupt_stale_preview_workers(path)
        self.thumbnail_request_id += 1
        request_id = self.thumbnail_request_id
        worker = PreviewThumbnailWorker(request_id, path)
        self.thumbnail_workers.append(worker)
        worker.loaded.connect(self.on_thumbnail_loaded)
        worker.failed.connect(self.on_thumbnail_failed)
        worker.finished.connect(lambda worker=worker: self.cleanup_thumbnail_worker(worker))
        worker.start()

    def schedule_video_poster_fallback(self, path: Path, delay_ms: int = 5000):
        self.cancel_video_poster_fallback(cancel_worker=True)
        self.interrupt_stale_preview_workers(path)
        # Invalidate artwork from the previous selection before waiting. Most
        # videos will paint a real frame and never launch the fallback worker.
        self.thumbnail_request_id += 1
        self.pending_video_poster_path = path
        self.video_poster_timer.start(max(0, int(delay_ms)))

    def on_video_frame_conversion_unavailable(self, reason: str):
        if self.media_player is None or self.video_widget is None or self.current_path is None:
            return
        if not is_video_path(self.current_path):
            return
        preview_trace(
            "embedded",
            "video frame conversion unavailable",
            self.current_path,
            force=True,
            request_id=self.playable_proxy_request_id,
            source_kind=preview_source_kind(self),
            decision="route through compatibility recovery",
            backend_message=_clean_process_diagnostic(reason, self.current_path, limit=500),
            has_frame=bool(self.video_widget.has_frame()),
            **video_frame_snapshot(self.video_widget),
            **qmedia_player_snapshot(self.media_player),
        )
        if self.playing_compatibility_proxy:
            self.fallback_from_unpaintable_proxy(Path(self.current_path), reason)
            return
        if self.current_path.suffix.lower() == ".webm":
            # QVideoWidget's native macOS surface is frequently black for VP8/
            # VP9 even though Qt reports successful playback.  A cached H.264
            # proxy is slower only on first use and gives WebM the same reliable
            # visual path as MP4 thereafter.
            path = Path(self.current_path)
            if not preview_proxy_running(self.playable_proxy_workers, path):
                QTimer.singleShot(
                    0,
                    lambda failed_path=path: self.start_compatible_video_preview(
                        failed_path,
                        autoplay=not self.logical_playback_paused(),
                    ) if self.current_path == failed_path else None,
                )
            return
        if self.video_widget.activate_native_fallback(self.media_player, reason):
            self.cancel_video_poster_fallback(cancel_worker=True)
            self.show_video_mode()
            return
        path = Path(self.current_path)
        if not preview_proxy_running(self.playable_proxy_workers, path):
            QTimer.singleShot(
                0,
                lambda failed_path=path: self.start_compatible_video_preview(
                    failed_path,
                    autoplay=not self.logical_playback_paused(),
                ) if self.current_path == failed_path else None,
            )

    def start_pending_video_poster(self):
        path = self.pending_video_poster_path
        self.pending_video_poster_path = None
        if (
            path is None
            or path != self.current_path
            or self.video_widget is None
            or self.video_widget.has_frame()
            or self.video_widget.using_native_fallback()
        ):
            return
        preview_trace(
            "embedded",
            "no-frame watchdog expired",
            path,
            force=True,
            request_id=self.playable_proxy_request_id,
            source_kind=preview_source_kind(self),
            decision="evaluate proxy/native/poster recovery",
            has_frame=False,
            has_poster=bool(getattr(self.video_widget, "_poster_image", None) is not None),
            **video_frame_snapshot(self.video_widget),
            **qmedia_player_snapshot(self.media_player),
        )
        if self.playing_compatibility_proxy:
            self.fallback_from_unpaintable_proxy(
                Path(path),
                "no paintable frame arrived from the compatibility proxy",
            )
            return
        if path.suffix.lower() == ".webm":
            self.start_compatible_video_preview(
                path,
                autoplay=not self.logical_playback_paused(),
            )
            return
        # First use Qt's direct surface. A transcode is reserved for a genuine
        # QMediaPlayer error, not a slow first frame.
        if self.video_widget.activate_native_fallback(self.media_player, "no convertible frame after loading"):
            return
        self.start_compatible_video_preview(path, autoplay=not self.logical_playback_paused())

    def cancel_video_poster_fallback(self, cancel_worker: bool = False):
        self.video_poster_timer.stop()
        path = self.pending_video_poster_path
        self.pending_video_poster_path = None
        if not cancel_worker:
            return
        path = path or self.current_path
        for worker in list(self.thumbnail_workers):
            if path is not None and getattr(worker, "path", None) != path:
                continue
            try:
                if worker.isRunning():
                    worker.cancel()
            except RuntimeError:
                pass

    def on_video_first_frame_ready(self):
        frame_key = (
            preview_item_id(self.current_path),
            self.playable_proxy_request_id,
            preview_source_kind(self),
        )
        if self._debug_first_frame_key != frame_key:
            self._debug_first_frame_key = frame_key
            image = getattr(self.video_widget, "_frame_image", None)
            try:
                frame_width = int(image.width()) if image is not None else 0
                frame_height = int(image.height()) if image is not None else 0
                pixel_format = qt_enum_name(image.format()) if image is not None else "unknown"
            except (AttributeError, RuntimeError, TypeError, ValueError):
                frame_width = 0
                frame_height = 0
                pixel_format = "unknown"
            preview_trace(
                "embedded",
                "first paintable video frame",
                self.current_path,
                force=True,
                request_id=self.playable_proxy_request_id,
                source_kind=preview_source_kind(self),
                decision="video widget now has visible media",
                frame_width=frame_width,
                frame_height=frame_height,
                pixel_format=pixel_format,
                elapsed_ms=(
                    round((time.monotonic() - self._debug_source_started_at) * 1000)
                    if self._debug_source_started_at > 0.0
                    else 0
                ),
                logical_paused=bool(self.logical_playback_paused()),
                **video_frame_snapshot(self.video_widget),
                **qmedia_player_snapshot(self.media_player),
            )
        self.cancel_video_poster_fallback(cancel_worker=True)
        if self.priming_paused_frame:
            self.priming_paused_frame = False
            self.media_playback_requested = False
            try:
                self.media_player.pause()
            except (AttributeError, RuntimeError):
                pass
            self.apply_preview_mute()
            self.set_video_dimmed(True)

    def prime_current_paused_video_frame(self):
        """Decode one silent frame before settling a newly selected video paused."""
        if self.media_player is None:
            self.set_video_dimmed(True)
            return
        self.priming_paused_frame = True
        self.media_playback_requested = False
        if self.audio_output is not None:
            try:
                self.audio_output.setMuted(True)
            except (AttributeError, RuntimeError):
                pass
        try:
            self.media_player.play()
        except (AttributeError, RuntimeError):
            self.priming_paused_frame = False
            self.apply_preview_mute()
        self.set_video_dimmed(True)

    def start_video_thumbnail(self, path: Path):
        self.interrupt_stale_preview_workers(path)
        self.thumbnail_request_id += 1
        request_id = self.thumbnail_request_id
        self.set_placeholder("Loading preview")

        worker = PreviewThumbnailWorker(request_id, path)
        self.thumbnail_workers.append(worker)
        worker.loaded.connect(self.on_thumbnail_loaded)
        worker.failed.connect(self.on_thumbnail_failed)
        worker.finished.connect(lambda worker=worker: self.cleanup_thumbnail_worker(worker))
        worker.start()

    def on_thumbnail_loaded(self, request_id: int, data: bytes):
        if request_id != self.thumbnail_request_id:
            return
        pixmap = QPixmap()
        pixmap.loadFromData(data)
        if self.current_path is not None:
            self.relay_poster_to_paired_preview(self.current_path, pixmap)
        preview_trace(
            "embedded",
            "preview poster ready",
            self.current_path,
            request_id=request_id,
            source_kind="extracted poster",
            decision="display while video source prepares" if is_video_path(self.current_path) else "display artwork",
            output_bytes=len(data),
        )
        if self.external_playback_owner is not None or self.poster_only:
            self.set_thumbnail_pixmap(pixmap)
            self.show_external_owner_mode()
            return
        if self.video_widget is not None and self.current_path and is_video_path(self.current_path):
            self.video_widget.set_poster_pixmap(pixmap)
            if self.media_player is not None:
                # Artwork is a retained poster for the video page.  A late
                # callback must never switch back to thumbnail mode and hide
                # the controls while the player is already active.
                self.show_video_mode()
                self.set_video_dimmed(self.logical_playback_paused())
                return
        self.set_thumbnail_pixmap(pixmap)
        if self.current_path is not None and self.current_path.suffix.lower() in AUDIO_EXTS:
            # Audio artwork arrives asynchronously after show_audio_mode().
            # Preserve the audio transport row instead of hiding it.
            self.show_audio_mode()
            self.set_video_dimmed(self.logical_playback_paused())

    def on_thumbnail_failed(self, request_id: int):
        if request_id == self.thumbnail_request_id:
            preview_trace(
                "embedded",
                "preview poster failed",
                self.current_path,
                force=True,
                request_id=request_id,
                source_kind="poster worker",
                decision="show media-type placeholder",
            )
            self.apply_artwork_pixmap(
                QPixmap(),
                kind_for_path(self.current_path) if self.current_path else "Media",
            )

    def cleanup_thumbnail_worker(self, worker: PreviewThumbnailWorker):
        if worker in self.thumbnail_workers:
            self.thumbnail_workers.remove(worker)
        worker.deleteLater()


# ---------------------------------------------------------------------------
# Reversible file operations and duplicate evidence


@dataclass
class ReviewMove:
    original: Path
    staged: Path


@dataclass
class TrashMove:
    original: Path
    trash: Path
    restored: Optional[Path] = None


@dataclass
class TrashAction:
    moves: List[TrashMove]


@dataclass
class FileOperationMove:
    before: Path
    after: Path


@dataclass
class BrowserAction:
    label: str
    moves: List[FileOperationMove]
    sends_to_trash: bool = False
    created_dirs: List[Path] = None

    def __post_init__(self):
        if self.created_dirs is None:
            self.created_dirs = []


class TrashMoveWorker(QThread):
    progress = Signal(int, int)
    results_ready = Signal(list, list)

    def __init__(self, paths: List[Path]):
        super().__init__()
        self.paths = list(dict.fromkeys(paths))

    def run(self):
        moves: List[TrashMove] = []
        failures: List[Path] = []
        total = len(self.paths)
        for index, path in enumerate(self.paths, start=1):
            if self.isInterruptionRequested():
                failures.extend(self.paths[index - 1 :])
                break
            try:
                move = move_to_trash_recorded(path)
                if move:
                    moves.append(move)
                else:
                    failures.append(path)
            except Exception:
                failures.append(path)
            self.progress.emit(index, total)
        self.results_ready.emit(moves, failures)


class OperationCancelled(Exception):
    pass


class RenameWorker(QThread):
    progress = Signal(str, int)
    renamed = Signal(object, object)
    results_ready = Signal(str, list)
    failed = Signal(str)
    cancelled = Signal(str, int)

    def __init__(self, label: str, rename_pairs: List[Tuple[Path, Path]]):
        super().__init__()
        self.label = label
        self.rename_pairs = rename_pairs
        self._cancel_requested = False

    def request_cancel(self):
        self._cancel_requested = True

    def check_cancel(self):
        if self._cancel_requested or self.isInterruptionRequested():
            raise OperationCancelled()

    def rollback_partial_operation(
        self,
        moves: List[FileOperationMove],
        temp_pairs: List[Tuple[Path, Path, Path]],
    ) -> int:
        rolled_back = 0
        for move in reversed(moves):
            if not move.after.exists():
                continue
            try:
                destination = move.before if not move.before.exists() else unique_path(move.before)
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.move(str(move.after), str(destination))
                rolled_back += 1
            except OSError:
                pass

        for original, temp, _dst in reversed(temp_pairs):
            if not temp.exists():
                continue
            try:
                destination = original if not original.exists() else unique_path(original)
                shutil.move(str(temp), str(destination))
                rolled_back += 1
            except OSError:
                pass
        return rolled_back

    def run(self):
        moves: List[FileOperationMove] = []
        temp_pairs: List[Tuple[Path, Path, Path]] = []
        try:
            total = max(1, len(self.rename_pairs))

            for index, (src, dst) in enumerate(self.rename_pairs, start=1):
                self.check_cancel()
                if not src.exists():
                    continue
                temp = src.with_name(f".folder_manager_tmp_{uuid.uuid4().hex}{src.suffix}")
                src.rename(temp)
                temp_pairs.append((src, temp, dst))
                self.progress.emit(
                    f"{self.label}: staging {index}/{total}",
                    int(45 * index / total),
                )

            final_total = max(1, len(temp_pairs))
            for index, (src, temp, dst) in enumerate(temp_pairs, start=1):
                self.check_cancel()
                final_dst = unique_path(dst)
                temp.rename(final_dst)
                move = FileOperationMove(before=src, after=final_dst)
                moves.append(move)
                self.renamed.emit(src, final_dst)
                self.progress.emit(
                    f"{self.label}: applying {index}/{final_total}",
                    45 + int(55 * index / final_total),
                )

            self.results_ready.emit(self.label, moves)
        except OperationCancelled:
            rolled_back = self.rollback_partial_operation(moves, temp_pairs)
            self.cancelled.emit(self.label, rolled_back)
        except Exception as exc:
            self.rollback_partial_operation(moves, temp_pairs)
            self.failed.emit(f"{type(exc).__name__}: {exc}")


@dataclass
class DupItem:
    group: int
    kind: str
    confidence: str
    file: Path
    details: str
    duration: str = ""
    sample_rate: str = ""
    resolution: str = ""
    duration_seconds: float = 0.0
    sample_rate_hz: int = 0
    width: int = 0
    height: int = 0
    quality_score: Tuple[float, float, float, float, float] = (0.0, 0.0, 0.0, 0.0, 0.0)
    source_evidence: Tuple[Tuple[int, str, str], ...] = ()
    health: str = "Safety check pending"
    health_issue: str = ""
    health_details: str = ""


DUPLICATE_HEALTH_PENDING = "Safety check pending"
DUPLICATE_HEALTH_VERIFIED = "Verified healthy"
DUPLICATE_HEALTH_UNVERIFIED = "Manual review needed"
DUPLICATE_HEALTH_DAMAGED = "Damaged"


def duplicate_evidence_rank(kind: str) -> int:
    """Use one evidence order in scanner results and their display groups."""
    ranks = {
        "Exact duplicate": 50,
        "Similar video": 42,
        "Similar image": 42,
        "Same cleaned name": 32,
        "Similar audio": 22,
    }
    return ranks.get(kind, 10)


def duplicate_health_rank(value: str) -> int:
    return {
        DUPLICATE_HEALTH_VERIFIED: 4,
        DUPLICATE_HEALTH_UNVERIFIED: 3,
        DUPLICATE_HEALTH_DAMAGED: 2,
        DUPLICATE_HEALTH_PENDING: 1,
    }.get(value, 0)


@lru_cache(maxsize=65536)
def canonical_duplicate_name_sort_key(path: Path) -> Tuple[int, int, int, int, str]:
    """Prefer a descriptive title over generated copy/download names."""
    stem = path.stem.strip()
    folded = stem.casefold()
    penalty = 0

    if strip_order_prefixes(stem) != stem:
        penalty += 2
    noisy_patterns = (
        r"(?:^|[\s._-])copy(?:[\s._-]*\d+)?(?:$|[\s._-])",
        r"(?:^|[\s._-])(?:duplicate|duplicated|dupe|dup)(?:$|[\s._-])",
        r"(?:^|[\s._-])(?:backup|temp|tmp|download)(?:$|[\s._-])",
        r"(?:^|[\s._-])(?:final[\s._-]*final|final[\s._-]*\d+)(?:$|[\s._-])",
    )
    penalty += 8 * sum(bool(re.search(pattern, folded)) for pattern in noisy_patterns)
    if re.search(r"(?:副本|拷贝|複製|コピー)", stem):
        penalty += 8
    if re.search(r"(?:\(\d+\)|\[\d+\]|[-_ ]\d+)$", folded):
        penalty += 5
    if re.search(r"[0-9a-f]{16,}", folded) or re.search(
        r"[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{8}",
        folded,
    ):
        penalty += 6
    if re.search(r"[._-]{2,}", stem):
        penalty += 2

    words = re.findall(r"[^\W_]+", stem, flags=re.UNICODE)
    letters = sum(character.isalpha() for character in stem)
    descriptive_words = sum(any(character.isalpha() for character in word) for word in words)
    # Lower tuples sort first: fewer copy markers, then more useful words and
    # letters. Length is only a late tie-breaker so a generated essay does not
    # beat a clean, ordinary title.
    return (penalty, -min(descriptive_words, 12), -min(letters, 120), len(stem), folded)


def duplicate_item_sort_key(item: DupItem) -> Tuple:
    quality = tuple(-float(value) for value in item.quality_score)
    return (
        -duplicate_health_rank(item.health),
        quality,
        canonical_duplicate_name_sort_key(item.file),
        natural_path_key(item.file),
        normalized_folder_path(item.file),
    )


def duplicate_group_has_meaningful_excerpt(group: Sequence[DupItem]) -> bool:
    video_durations = [
        candidate.duration_seconds
        for candidate in group
        if candidate.duration_seconds > 0 and kind_for_path(candidate.file) == "Video"
    ]
    return bool(
        len(video_durations) >= 2
        and min(video_durations) / max(video_durations) < 0.92
    )


def duplicate_group_item_sort_key(
    item: DupItem,
    group: Sequence[DupItem],
    has_meaningful_excerpt: Optional[bool] = None,
) -> Tuple:
    if has_meaningful_excerpt is None:
        has_meaningful_excerpt = duplicate_group_has_meaningful_excerpt(group)
    if not has_meaningful_excerpt:
        return duplicate_item_sort_key(item)
    # Within an excerpt family, the complete timeline is the original. Health
    # still outranks completeness, so a damaged full-length file never beats a
    # verified shorter copy.
    quality = tuple(-float(value) for value in item.quality_score)
    return (
        -duplicate_health_rank(item.health),
        -float(item.duration_seconds),
        quality,
        canonical_duplicate_name_sort_key(item.file),
        natural_path_key(item.file),
        normalized_folder_path(item.file),
    )


def order_duplicate_items(items: Iterable[DupItem]) -> List[DupItem]:
    by_group: Dict[int, List[DupItem]] = defaultdict(list)
    for item in items:
        by_group[item.group].append(item)
    ordered: List[DupItem] = []
    for group_id in sorted(by_group):
        group = by_group[group_id]
        has_excerpt = duplicate_group_has_meaningful_excerpt(group)
        ordered.extend(sorted(
            group,
            key=lambda item: duplicate_group_item_sort_key(item, group, has_excerpt),
        ))
    return ordered


def duplicate_deletion_safety_message(
    groups: Iterable[Sequence[DupItem]],
    selected_paths: Iterable[Path],
) -> str:
    selected = {normalized_folder_path(path) for path in selected_paths}
    for group in groups:
        existing = [item for item in group if item.file.exists()]
        chosen = [item for item in existing if normalized_folder_path(item.file) in selected]
        if not chosen:
            continue
        if any(item.health == DUPLICATE_HEALTH_PENDING for item in existing):
            return (
                "This duplicate family has not finished its damage checks. You can keep working "
                "in other fully checked groups while these rows finish."
            )
        remaining = [item for item in existing if normalized_folder_path(item.file) not in selected]
        if not remaining:
            return (
                "That selection would delete every available copy in a duplicate family. Keep at "
                "least one file."
            )
        if (
            any(item.health == DUPLICATE_HEALTH_VERIFIED for item in chosen)
            and not any(item.health == DUPLICATE_HEALTH_VERIFIED for item in remaining)
        ):
            return (
                "That selection would remove the last verified healthy copy and leave only "
                "damaged or unverified files. Keep at least one verified healthy copy."
            )
    return ""


def apply_duplicate_metadata(item: DupItem, meta: MediaMeta):
    item.duration = meta.duration
    item.sample_rate = meta.sample_rate
    item.resolution = meta.resolution
    item.duration_seconds = meta.duration_seconds
    item.sample_rate_hz = meta.sample_rate_hz
    item.width = meta.width
    item.height = meta.height
    item.quality_score = quality_score_for_path(item.file, meta)


# ---------------------------------------------------------------------------
# Duplicate scanning


class DuplicateWorker(QThread):
    progress = Signal(str, int)
    partial = Signal(list)
    metadata_ready = Signal(object, object)
    health_ready = Signal(object, object)
    results_ready = Signal(list)
    failed = Signal(str)
    cancelled = Signal()

    def __init__(self, folder: Path, deep_media: bool = False, scan_files: Optional[List[Path]] = None):
        super().__init__()
        register_scan_worker(self)
        self.folder = folder
        self.deep_media = deep_media
        self.scan_files = list(scan_files) if scan_files is not None else None
        self._cancel_requested = False
        self._metadata_cache: Dict[Path, MediaMeta] = {}
        metadata_workers = max(3, min(8, os.cpu_count() or 8))
        self._metadata_executor = concurrent.futures.ThreadPoolExecutor(
            max_workers=metadata_workers,
            thread_name_prefix="folder-manager-metadata",
        )
        self._metadata_futures: Dict[Path, concurrent.futures.Future] = {}
        self._video_sequence_cache: Dict[Path, List[str]] = {}
        self._deep_video_fingerprint_cache: Dict[Path, Optional[VideoFingerprint]] = {}
        self._audio_signature_cache: Dict[Path, Optional[str]] = {}
        self._last_partial_emit = 0.0
        self._health_lock = threading.RLock()
        self._health_cache: Dict[str, Tuple[str, str, str]] = {}
        self._health_futures: Dict[str, Tuple[Path, concurrent.futures.Future]] = {}
        self._health_executor = concurrent.futures.ThreadPoolExecutor(
            max_workers=max(1, min(2, SCAN_MEDIA_WORKERS)),
            thread_name_prefix="folder-manager-duplicate-health",
        )
        self._allowed_removed_lock = threading.RLock()
        self._allowed_removed_paths: set[Path] = set()

    def run(self):
        try:
            run_scan_task(self, self.run_scan)
        except ScanCancelled:
            self.cancelled.emit()
        except Exception as exc:
            debug_log("duplicate-scan", "worker failed", error_type=type(exc).__name__, error=str(exc))
            self.failed.emit(
                str(exc).strip()
                or "The duplicate scan stopped because of an unexpected internal error."
            )
        finally:
            cancel_scan_processes(self)
            self._metadata_executor.shutdown(wait=False, cancel_futures=True)
            self._health_executor.shutdown(wait=False, cancel_futures=True)

    def request_cancel(self):
        self._cancel_requested = True
        cancel_scan_processes(self)

    def check_cancel(self):
        if self._cancel_requested or self.isInterruptionRequested():
            raise ScanCancelled()

    def allow_paths_removed(self, paths: Iterable[Path]):
        """Permit exact scanner-owned Trash moves without hiding other changes."""
        with self._allowed_removed_lock:
            self._allowed_removed_paths.update(Path(path) for path in paths)

    def allowed_removed_paths(self) -> set[Path]:
        with self._allowed_removed_lock:
            return set(self._allowed_removed_paths)

    def path_was_intentionally_removed(self, path: Path) -> bool:
        with self._allowed_removed_lock:
            allowed = path in self._allowed_removed_paths
        return allowed and not path.exists()

    def verify_scan_scope_unchanged(self, files: Sequence[Path]):
        if self.scan_files is not None:
            return
        self.progress.emit("Confirming the folder did not change during the scan…", -1)
        stable = False
        change_count = 0
        # A Trash action can finish during the re-enumeration itself. Retry once
        # with the newest allow-list before classifying that deliberate removal
        # as an external folder mutation.
        for _attempt in range(2):
            stable, change_count = recursive_file_set_is_stable(
                self.folder,
                files,
                cancel_check=self.check_cancel,
                allowed_missing_paths=self.allowed_removed_paths(),
            )
            if stable:
                break
        if not stable:
            raise RuntimeError(
                "The folder changed or became partly inaccessible while the duplicate scan was "
                f"running ({human_count(change_count)} changed or unreadable location(s)). The "
                "scan stopped instead of presenting a stale result. Wait for file operations to "
                "finish, then run it again."
            )

    def strongest_confidence(self, values: Iterable[str]) -> str:
        ranks = {"Low": 1, "Medium": 2, "Medium/High": 3, "High": 4, "Certain": 5}
        values = [value for value in values if value]
        if not values:
            return ""
        return max(values, key=lambda value: ranks.get(value, 0))

    def merge_duplicate_groups(self, groups: List[DupItem]) -> List[DupItem]:
        by_group: Dict[int, List[DupItem]] = defaultdict(list)
        for item in groups:
            if item.file.exists():
                by_group[item.group].append(item)

        # Evidence arrives mostly as matched pairs. Treat it as a graph: A-B and
        # B-C are one duplicate family even when two separately re-encoded copies
        # (A and C) miss the direct threshold. Connected components also make the
        # membership rule explicit: a path belongs to exactly one group header.
        evidence_sets: List[Tuple[int, List[str], List[DupItem]]] = []
        records_by_path: Dict[str, List[DupItem]] = defaultdict(list)
        parent: Dict[str, str] = {}

        def find(path_key: str) -> str:
            parent.setdefault(path_key, path_key)
            while parent[path_key] != path_key:
                parent[path_key] = parent[parent[path_key]]
                path_key = parent[path_key]
            return path_key

        def union(left: str, right: str):
            left_root = find(left)
            right_root = find(right)
            if left_root == right_root:
                return
            if left_root < right_root:
                parent[right_root] = left_root
            else:
                parent[left_root] = right_root

        for evidence_id, items in by_group.items():
            unique_by_path: Dict[str, DupItem] = {}
            for item in items:
                if not item.file.exists():
                    continue
                path_key = normalized_folder_path(item.file)
                unique_by_path.setdefault(path_key, item)
                records_by_path[path_key].append(item)
            path_keys = sorted(unique_by_path)
            if len(path_keys) < 2:
                continue
            evidence_sets.append((evidence_id, path_keys, list(unique_by_path.values())))
            first_path = path_keys[0]
            find(first_path)
            for path_key in path_keys[1:]:
                union(first_path, path_key)

        component_paths: Dict[str, List[str]] = defaultdict(list)
        for path_key in records_by_path:
            if path_key in parent:
                component_paths[find(path_key)].append(path_key)
        clusters = [sorted(paths) for paths in component_paths.values() if len(paths) >= 2]

        normalized: List[DupItem] = []
        clusters.sort(
            key=lambda cluster: min(
                evidence_id
                for evidence_id, paths, _records in evidence_sets
                if len(set(paths) & set(cluster)) >= 2
            )
        )
        for cluster in clusters:
            cluster_paths = set(cluster)
            relevant_sets = [
                evidence
                for evidence in evidence_sets
                if len(cluster_paths & set(evidence[1])) >= 2
            ]
            if not relevant_sets:
                continue
            relevant_evidence_ids = {evidence[0] for evidence in relevant_sets}
            records = [
                record
                for path_key in cluster
                for record in records_by_path[path_key]
                if record.group in relevant_evidence_ids
            ]
            by_path: Dict[str, List[DupItem]] = defaultdict(list)
            for item in records:
                path_key = normalized_folder_path(item.file)
                if path_key in cluster_paths:
                    by_path[path_key].append(item)
            if len(by_path) < 2:
                continue

            group_id = min(evidence[0] for evidence in relevant_sets)
            group_evidence = sorted(
                {item.kind for item in records if item.kind},
                key=duplicate_evidence_rank,
                reverse=True,
            )
            group_kind = " + ".join(group_evidence[:3]) if group_evidence else "Duplicate"
            confidence = self.strongest_confidence(item.confidence for item in records)

            for path_key in sorted(by_path):
                path_records = by_path[path_key]
                representative = path_records[0]
                details = sorted({record.details for record in path_records if record.details})
                evidence = sorted({record.kind for record in path_records if record.kind})
                # The connected duplicate family is the useful grouping boundary.
                # Give every row the same cluster evidence id so pairwise scan
                # order cannot split it into separate subheaders.
                source_evidence = tuple(
                    (group_id, str(kind or ""), "coherent direct-match cluster")
                    for kind in group_evidence[:3]
                )
                normalized.append(
                    DupItem(
                        group_id,
                        group_kind,
                        confidence,
                        representative.file,
                        " | ".join(details[:3]) or " + ".join(evidence[:3]),
                        duration=representative.duration,
                        sample_rate=representative.sample_rate,
                        resolution=representative.resolution,
                        duration_seconds=representative.duration_seconds,
                        sample_rate_hz=representative.sample_rate_hz,
                        width=representative.width,
                        height=representative.height,
                        quality_score=representative.quality_score,
                        source_evidence=source_evidence,
                        health=representative.health,
                        health_issue=representative.health_issue,
                        health_details=representative.health_details,
                    )
                )

        # A path can only occur once because components partition graph nodes.
        # Keep this defensive pass in case malformed caller data repeats a row.
        unique: List[DupItem] = []
        seen_paths: set[str] = set()
        for item in order_duplicate_items(normalized):
            path_key = normalized_folder_path(item.file)
            if path_key in seen_paths:
                continue
            seen_paths.add(path_key)
            unique.append(item)
        return unique

    def video_hashes_match(
        self,
        path_a: Path,
        fingerprint_a: VideoFingerprint,
        path_b: Path,
        fingerprint_b: VideoFingerprint,
    ) -> bool:
        hashes_a = list(fingerprint_a.hashes)
        hashes_b = list(fingerprint_b.hashes)
        distances = [hamming_hex(a, b) for a, b in zip(hashes_a, hashes_b)]
        if len(distances) < 5:
            return False
        if len(fingerprint_a.average_rgb) != len(hashes_a) or len(fingerprint_b.average_rgb) != len(hashes_b):
            return False
        color_distances = [
            sum((left - right) ** 2 for left, right in zip(color_a, color_b)) ** 0.5
            for color_a, color_b in zip(fingerprint_a.average_rgb, fingerprint_b.average_rgb)
        ]
        shorter_duration = min(fingerprint_a.duration, fingerprint_b.duration)
        longer_duration = max(fingerprint_a.duration, fingerprint_b.duration)
        duration_ratio = shorter_duration / longer_duration if longer_duration > 0 else 0.0

        # Near-equal videos should agree at aligned beginning, middle, and end
        # samples. This is deliberately stricter than a single thumbnail match.
        if duration_ratio >= 0.85:
            close_count = sum(1 for distance in distances if distance <= 7)
            close_color_count = sum(1 for distance in color_distances if distance <= 55.0)
            aligned_match = (
                sum(distances) / len(distances) <= 6.0
                and max(distances) <= 12
                and close_count >= max(5, int(len(distances) * 0.80 + 0.999))
                and sum(color_distances) / len(color_distances) <= 45.0
                and close_color_count >= max(5, int(len(color_distances) * 0.80 + 0.999))
                and distances[0] <= 9
                and distances[-1] <= 9
            )
            if aligned_match:
                return True
            # Do not let the looser excerpt path override a failed aligned check
            # for videos that claim nearly the same duration.
            return False

        # A duration mismatch can be legitimate when one file is an excerpt.
        # Confirm that case with an ordered keyframe sequence instead of either
        # rejecting it or trusting coincidentally similar sampled frames.
        cross_matches = sum(
            1
            for value in hashes_a
            if min((hamming_hex(value, other) for other in hashes_b), default=999999) <= 10
        )
        # Two coarse visual hits justify the expensive ordered keyframe check.
        # The keyframe sequence remains the actual excerpt decision.
        if cross_matches < 2:
            return False
        short_path, long_path = (
            (path_a, path_b)
            if fingerprint_a.duration <= fingerprint_b.duration
            else (path_b, path_a)
        )
        short_sequence = self._video_sequence_cache.get(short_path)
        if short_sequence is None:
            short_sequence = video_keyframe_phashes(short_path)
            self._video_sequence_cache[short_path] = short_sequence
        long_sequence = self._video_sequence_cache.get(long_path)
        if long_sequence is None:
            long_sequence = video_keyframe_phashes(long_path)
            self._video_sequence_cache[long_path] = long_sequence
        if not short_sequence or not long_sequence:
            raise RuntimeError(
                "A possible excerpt match could not complete its ordered keyframe check. The "
                "scan stopped instead of silently omitting that possible duplicate."
            )
        return ordered_video_sequence_match(short_sequence, long_sequence)

    def video_audio_tracks_match(self, path_a: Path, path_b: Path) -> bool:
        """Prevent visually identical videos with different soundtracks from matching."""
        meta_a = scanner_media_metadata(path_a)
        meta_b = scanner_media_metadata(path_b)
        if not meta_a.video_codec or not meta_b.video_codec:
            raise RuntimeError(
                "A possible video pair could not complete its stream check. The scan stopped "
                "instead of accepting a visual-only result with unknown audio content."
            )
        has_audio_a = bool(meta_a.audio_codec or meta_a.sample_rate_hz)
        has_audio_b = bool(meta_b.audio_codec or meta_b.sample_rate_hz)
        if has_audio_a != has_audio_b:
            return False
        if not has_audio_a:
            return True

        for path in (path_a, path_b):
            if path not in self._audio_signature_cache:
                self._audio_signature_cache[path] = audio_signature(path)
        signature_a = self._audio_signature_cache[path_a]
        signature_b = self._audio_signature_cache[path_b]
        if not signature_a or not signature_b:
            raise RuntimeError(
                "A possible video pair had audio tracks, but their audio confirmation did not "
                "finish. The scan stopped instead of relying on matching pictures alone."
            )
        return (
            len(signature_a) == len(signature_b)
            and hamming_hex(signature_a, signature_b) <= 12
        )

    def audio_files_match(
        self,
        path_a: Path,
        signature_a: str,
        path_b: Path,
        signature_b: str,
    ) -> bool:
        """Require both fingerprint and near-complete duration for audio duplicates."""
        if len(signature_a) != len(signature_b) or hamming_hex(signature_a, signature_b) > 12:
            return False
        meta_a = scanner_media_metadata(path_a)
        meta_b = scanner_media_metadata(path_b)
        duration_a = float(meta_a.duration_seconds or 0.0)
        duration_b = float(meta_b.duration_seconds or 0.0)
        if duration_a <= 0 or duration_b <= 0:
            raise RuntimeError(
                "A possible audio pair could not complete its duration check. The scan stopped "
                "instead of treating a partial or unknown-length track as a full duplicate."
            )
        shorter = min(duration_a, duration_b)
        longer = max(duration_a, duration_b)
        return shorter / longer >= 0.94 and longer - shorter <= max(6.0, longer * 0.06)

    def apply_cached_health(self, items: Iterable[DupItem]):
        with self._health_lock:
            cache = dict(self._health_cache)
        for item in items:
            result = cache.get(normalized_folder_path(item.file))
            if result is not None:
                item.health, item.health_issue, item.health_details = result

    def health_check_result(self, path: Path) -> Tuple[str, str, str]:
        try:
            return duplicate_health_check(path)
        except ScanCancelled:
            raise
        except Exception as exc:
            return (
                DUPLICATE_HEALTH_UNVERIFIED,
                "Check did not finish",
                f"The damage check stopped unexpectedly ({type(exc).__name__}). Review this file manually.",
            )

    def on_health_future_done(
        self,
        path: Path,
        future: concurrent.futures.Future,
    ):
        try:
            result = future.result()
        except (ScanCancelled, concurrent.futures.CancelledError):
            return
        except Exception as exc:
            result = (
                DUPLICATE_HEALTH_UNVERIFIED,
                "Check did not finish",
                f"The damage check stopped unexpectedly ({type(exc).__name__}). Review this file manually.",
            )
        with self._health_lock:
            self._health_cache[normalized_folder_path(path)] = result
        if self._cancel_requested:
            return
        try:
            if not self.isInterruptionRequested():
                self.health_ready.emit(path, result)
        except RuntimeError:
            return

    def schedule_duplicate_health(self, items: Iterable[DupItem]):
        """Start bad-file checks as soon as a duplicate path becomes visible."""
        for path in dict.fromkeys(item.file for item in items if item.file.exists()):
            self.check_cancel()
            path_key = normalized_folder_path(path)
            with self._health_lock:
                if path_key in self._health_cache or path_key in self._health_futures:
                    continue
                future = self._health_executor.submit(
                    run_scan_task,
                    self,
                    self.health_check_result,
                    path,
                )
                self._health_futures[path_key] = (path, future)
            future.add_done_callback(
                lambda completed, media_path=path: self.on_health_future_done(media_path, completed)
            )

    def emit_partial(self, groups: List[DupItem], force: bool = False):
        self.check_cancel()
        now = time.monotonic()
        row_count = len(groups)
        if row_count > 4000:
            minimum_interval = 2.0
        elif row_count > 2000:
            minimum_interval = 1.4
        elif row_count > 800:
            minimum_interval = 0.9
        elif row_count > 250:
            minimum_interval = 0.9
        else:
            minimum_interval = 0.75
        if not force and now - self._last_partial_emit < minimum_interval:
            return
        self._last_partial_emit = now
        partial = self.merge_duplicate_groups(groups)
        # Duplicate discovery continues in this worker while a separate bounded
        # executor runs the exact same checks as Bad File Scan. Rows therefore
        # gain health state incrementally instead of waiting for the final stage.
        self.schedule_duplicate_health(partial)
        self.apply_cached_health(partial)
        self.attach_media_metadata(partial, emit_progress=False)
        self.partial.emit(partial)

    def validate_duplicate_group_health(self, groups: List[DupItem]):
        """Finish any progressive checks still pending before the final payload."""
        paths = list(dict.fromkeys(item.file for item in groups if item.file.exists()))
        if not paths:
            return
        self.schedule_duplicate_health(groups)
        path_keys = {normalized_folder_path(path) for path in paths}
        progress_estimate = ScannerProgressEstimate(paths)
        accounted_paths: set[str] = set()
        while True:
            self.check_cancel()
            with self._health_lock:
                entries = [
                    (path_key, path, future)
                    for path_key, (path, future) in self._health_futures.items()
                    if path_key in path_keys
                ]
            # Future.wait() may wake just before a done callback stores its
            # result. Harvest completed futures here too so the final payload
            # can never regress a live row back to "Checking…".
            for path_key, _path, future in entries:
                with self._health_lock:
                    already_cached = path_key in self._health_cache
                if already_cached or not future.done():
                    continue
                try:
                    result = future.result()
                except (ScanCancelled, concurrent.futures.CancelledError):
                    raise ScanCancelled()
                except Exception as exc:
                    result = (
                        DUPLICATE_HEALTH_UNVERIFIED,
                        "Check did not finish",
                        f"The damage check stopped unexpectedly ({type(exc).__name__}). Review this file manually.",
                    )
                with self._health_lock:
                    self._health_cache.setdefault(path_key, result)
            with self._health_lock:
                pending = [future for _path_key, _path, future in entries if not future.done()]
                completed_paths = {
                    path_key for path_key in path_keys if path_key in self._health_cache
                }
            for path_key, path, _future in entries:
                if path_key in completed_paths and path_key not in accounted_paths:
                    progress_estimate.complete(path)
                    accounted_paths.add(path_key)
            completed = len(completed_paths)
            if not pending:
                break
            concurrent.futures.wait(
                pending,
                timeout=0.15,
                return_when=concurrent.futures.FIRST_COMPLETED,
            )
            self.progress.emit(
                f"Safety checks: {human_count(completed)}/{human_count(len(paths))} complete "
                f"• duplicate discovery remains usable • {progress_estimate.eta_text()}",
                97 + int(2 * progress_estimate.percent() / 100),
            )
        self.apply_cached_health(groups)

    def ensure_metadata_future(self, path: Path) -> Optional[concurrent.futures.Future]:
        if path in self._metadata_cache:
            return None
        future = self._metadata_futures.get(path)
        if future is not None:
            return future
        future = self._metadata_executor.submit(
            run_scan_task,
            self,
            scanner_media_metadata,
            path,
        )
        self._metadata_futures[path] = future
        future.add_done_callback(lambda completed, media_path=path: self.on_metadata_future_done(media_path, completed))
        return future

    def on_metadata_future_done(self, path: Path, future: concurrent.futures.Future):
        try:
            meta = future.result()
        except Exception:
            return
        self._metadata_cache[path] = meta
        if self._cancel_requested:
            return
        try:
            if self.isInterruptionRequested():
                return
            self.metadata_ready.emit(path, meta)
        except RuntimeError:
            return

    def map_paths_concurrently(
        self,
        paths: List[Path],
        label: str,
        progress_base: int,
        progress_span: int,
        fn,
        on_result: Optional[Callable[[Path, object], None]] = None,
        require_result: bool = False,
    ):
        results = []
        total = max(1, len(paths))
        progress_estimate = ScannerProgressEstimate(paths)
        cpu_count = os.cpu_count() or 8
        if label in {"Video frames", "Audio"}:
            # Each video fingerprint fans out to several FFmpeg inputs. Ten
            # Python workers therefore caused storage contention and exhausted
            # VideoToolbox sessions on large external-drive scans.
            max_workers = min(SCAN_MEDIA_WORKERS, cpu_count)
        else:
            max_workers = max(4, min(12, cpu_count))
        pending: Dict[concurrent.futures.Future, Path] = {}
        failed_paths: List[Path] = []
        iterator = iter(paths)
        completed = 0
        executor = concurrent.futures.ThreadPoolExecutor(
            max_workers=max_workers,
            thread_name_prefix=f"folder-manager-{label.casefold().replace(' ', '-')}",
        )
        last_heartbeat_at = 0.0
        try:
            def submit_until_full():
                nonlocal completed
                while len(pending) < max_workers * 2:
                    self.check_cancel()
                    try:
                        path = next(iterator)
                    except StopIteration:
                        return
                    if self.path_was_intentionally_removed(path):
                        completed += 1
                        continue
                    pending[executor.submit(run_scan_task, self, fn, path)] = path

            submit_until_full()
            while pending:
                self.check_cancel()
                done, _not_done = concurrent.futures.wait(
                    pending,
                    timeout=0.15,
                    return_when=concurrent.futures.FIRST_COMPLETED,
                )
                if not done:
                    now = time.monotonic()
                    if now - last_heartbeat_at >= 0.75:
                        last_heartbeat_at = now
                        active = min(max_workers, len(pending))
                        self.progress.emit(
                            f"{label}: {human_count(completed)}/{human_count(len(paths))} complete "
                            f"• {active} active • {progress_estimate.eta_text()}",
                            progress_base + int(progress_span * progress_estimate.percent() / 100),
                        )
                    continue
                for future in done:
                    path = pending.pop(future)
                    completed += 1
                    try:
                        result = future.result()
                    except ScanCancelled:
                        raise
                    except Exception:
                        if not self.path_was_intentionally_removed(path):
                            failed_paths.append(path)
                        result = None
                    if (
                        result is None
                        and require_result
                        and path not in failed_paths
                        and not self.path_was_intentionally_removed(path)
                    ):
                        failed_paths.append(path)
                    if result is not None and not self.path_was_intentionally_removed(path):
                        results.append((path, result))
                        if on_result is not None:
                            on_result(path, result)
                    progress_estimate.complete(path)
                    self.progress.emit(
                        f"{progress_estimate.text(label, total, path.name)} | {max_workers} workers",
                        progress_base + int(progress_span * progress_estimate.percent() / 100),
                    )
                submit_until_full()
        except ScanCancelled:
            executor.shutdown(wait=False, cancel_futures=True)
            raise
        finally:
            executor.shutdown(wait=False, cancel_futures=True)
        failed_paths = [path for path in failed_paths if not self.path_was_intentionally_removed(path)]
        if failed_paths:
            raise RuntimeError(
                f"The {label.casefold()} stage could not check "
                f"{human_count(len(failed_paths))} file(s). The duplicate scan stopped instead of "
                "showing incomplete results. Make sure the files are stable and readable, then "
                "run it again."
            )
        return results

    def run_scan(self):
        scan_started_at = time.time()
        self.progress.emit("Finding files to check…", -1)

        def report_enumeration(count: int, _folder: Path):
            self.progress.emit(f"Finding files… {human_count(count)} found", -1)

        discovery_errors: List[OSError] = []
        files = (
            list(self.scan_files)
            if self.scan_files is not None
            else list_files_recursive(
                self.folder,
                progress_callback=report_enumeration,
                cancel_check=self.check_cancel,
                error_callback=discovery_errors.append,
            )
        )
        if discovery_errors:
            raise RuntimeError(
                "Folder Manager could not read "
                f"{human_count(len(discovery_errors))} folder location(s), so the duplicate scan "
                "stopped instead of showing incomplete results. Check folder permissions and disk "
                "connections, then run it again."
            )
        if self.deep_media:
            video_file_count = sum(1 for path in files if is_video_path(path))
            audio_file_count = sum(1 for path in files if path.suffix.lower() in AUDIO_EXTS)
            image_file_count = sum(1 for path in files if path.suffix.lower() in IMAGE_EXTS)
            missing_tools = []
            if (video_file_count or audio_file_count) and ffmpeg_path() is None:
                missing_tools.append("FFmpeg")
            if video_file_count and ffprobe_path() is None:
                missing_tools.append("ffprobe")
            if image_file_count:
                try:
                    from PIL import Image as Image  # Verify the optional decoder can import. - verify optional decoder availability
                    import numpy as numpy  # Verify the optional fingerprint dependency. - verify optional fingerprint dependency
                except ImportError:
                    missing_tools.append("Pillow and NumPy")
            if missing_tools:
                affected_count = video_file_count + audio_file_count + image_file_count
                tools_text = ", ".join(dict.fromkeys(missing_tools))
                raise RuntimeError(
                    f"Folder Manager found {human_count(affected_count)} media file(s), but the "
                    f"deep duplicate checks need {tools_text}. The scan stopped instead of "
                    "showing incomplete results that could miss duplicates. Install the missing "
                    "media tools and run the scan again."
                )
        groups: List[DupItem] = []
        group_id = 1

        self.progress.emit(f"Scanning {human_count(len(files))} recursive file(s)", 3)
        self.check_cancel()

        # Do not create duplicate groups from cleaned names alone. Stripping a
        # leading ordering number can make unrelated files look duplicated
        # (for example, renumbered music/video libraries), so duplicates now require
        # byte-identical hashes or real media similarity evidence.
        self.progress.emit("Checking exact SHA-256 duplicates", 20)
        by_size: Dict[int, List[Path]] = defaultdict(list)
        unreadable_size_paths: List[Path] = []
        for p in files:
            self.check_cancel()
            try:
                by_size[p.stat().st_size].append(p)
            except OSError:
                unreadable_size_paths.append(p)
        if unreadable_size_paths:
            raise RuntimeError(
                "Folder Manager could not read the size of "
                f"{human_count(len(unreadable_size_paths))} file(s). The duplicate scan stopped "
                "instead of skipping them. Make sure the files still exist and are readable, then "
                "run it again."
            )

        candidate_files = [p for same_size in by_size.values() if len(same_size) > 1 for p in same_size]
        by_hash: Dict[str, List[Path]] = defaultdict(list)
        hash_group_by_digest: Dict[str, int] = {}
        exact_digest_by_path: Dict[str, str] = {}

        def on_hash_result(path: Path, digest: object):
            nonlocal group_id
            if self.path_was_intentionally_removed(path):
                return
            digest_text = str(digest)
            exact_digest_by_path[normalized_folder_path(path)] = digest_text
            existing = by_hash[digest_text]
            if existing:
                live_group_id = hash_group_by_digest.get(digest_text)
                if live_group_id is None:
                    live_group_id = group_id
                    group_id += 1
                    hash_group_by_digest[digest_text] = live_group_id
                    for existing_path in existing:
                        groups.append(DupItem(live_group_id, "Exact duplicate", "Certain", existing_path, digest_text[:16]))
                groups.append(DupItem(live_group_id, "Exact duplicate", "Certain", path, digest_text[:16]))
                self.emit_partial(groups)
            existing.append(path)

        def paths_are_already_exact_duplicates(left: Path, right: Path) -> bool:
            left_digest = exact_digest_by_path.get(normalized_folder_path(left))
            return bool(
                left_digest
                and left_digest == exact_digest_by_path.get(normalized_folder_path(right))
            )

        self.map_paths_concurrently(
            candidate_files,
            "Hashing",
            20,
            25,
            sha256_file,
            on_result=on_hash_result,
            require_result=True,
        )
        self.emit_partial(groups, force=True)

        if not self.deep_media:
            groups = self.merge_duplicate_groups(groups)
            self.validate_duplicate_group_health(groups)
            self.attach_media_metadata(groups)
            groups = order_duplicate_items(groups)
            self.verify_scan_scope_unchanged(files)
            self.progress.emit(f"Done in {format_eta(time.time() - scan_started_at)}", 100)
            self.results_ready.emit(groups)
            return

        self.progress.emit("Checking similar images", 50)
        image_files = [
            p
            for p in files
            if p.suffix.lower() in IMAGE_EXTS
            and p.exists()
            and not self.path_was_intentionally_removed(p)
        ]
        image_hashes: Dict[Path, ImageFingerprint] = {}
        image_hash_index = PerceptualHashBandIndex(8)

        def on_image_result(path: Path, hash_value: object):
            nonlocal group_id
            if (
                not isinstance(hash_value, ImageFingerprint)
                or self.path_was_intentionally_removed(path)
            ):
                return
            fingerprint = hash_value
            candidate_paths = {
                candidate_path
                for candidate_path, _hash_index in image_hash_index.candidates(fingerprint.phash)
                if candidate_path.exists()
                and not self.path_was_intentionally_removed(candidate_path)
            }
            matches = [
                (other_path, image_hashes[other_path])
                for other_path in candidate_paths
                if other_path in image_hashes
                and not paths_are_already_exact_duplicates(path, other_path)
                for other_fingerprint in [image_hashes[other_path]]
                if image_fingerprints_match(fingerprint, other_fingerprint)
            ]
            if matches:
                for matched_path, matched_fingerprint in matches:
                    live_group_id = group_id
                    group_id += 1
                    groups.append(
                        DupItem(
                            live_group_id,
                            "Similar image",
                            "High",
                            matched_path,
                            matched_fingerprint.phash,
                        )
                    )
                    groups.append(
                        DupItem(live_group_id, "Similar image", "High", path, fingerprint.phash)
                    )
                self.emit_partial(groups)
            image_hashes[path] = fingerprint
            image_hash_index.add(fingerprint.phash, (path, 0))

        self.map_paths_concurrently(
            image_files,
            "Images",
            50,
            10,
            image_phash,
            on_result=on_image_result,
            require_result=True,
        )
        self.emit_partial(groups, force=True)

        self.progress.emit("Checking similar videos", 62)
        video_files = [
            p
            for p in files
            if is_video_path(p)
            and p.exists()
            and not self.path_was_intentionally_removed(p)
        ]
        video_hashes: Dict[Path, VideoFingerprint] = {}
        video_hash_index = PerceptualHashBandIndex(10)

        def on_video_result(path: Path, hashes: object):
            nonlocal group_id
            if (
                not isinstance(hashes, VideoFingerprint)
                or self.path_was_intentionally_removed(path)
            ):
                return
            fingerprint = hashes
            matches: List[Tuple[Path, VideoFingerprint, VideoFingerprint]] = []
            candidate_votes: Dict[Path, int] = defaultdict(int)
            for hash_text in fingerprint.hashes:
                matched_paths_for_frame: set[Path] = set()
                for candidate_path, hash_index in video_hash_index.candidates(hash_text):
                    other_fingerprint = video_hashes.get(candidate_path)
                    if other_fingerprint is None or hash_index >= len(other_fingerprint.hashes):
                        continue
                    if hamming_hex(hash_text, other_fingerprint.hashes[hash_index]) <= 10:
                        matched_paths_for_frame.add(candidate_path)
                for candidate_path in matched_paths_for_frame:
                    candidate_votes[candidate_path] += 1
            # video_hashes_match requires at least two coarse visual hits before
            # its ordered excerpt confirmation. Avoid invoking it for candidates
            # that cannot possibly pass that unchanged rule.
            candidate_paths = {
                candidate_path
                for candidate_path, votes in candidate_votes.items()
                if votes >= 2
                and candidate_path.exists()
                and not self.path_was_intentionally_removed(candidate_path)
                and not paths_are_already_exact_duplicates(path, candidate_path)
            }
            for other_path in candidate_paths:
                other_coarse_fingerprint = video_hashes.get(other_path)
                if other_coarse_fingerprint is None:
                    continue
                # Only plausible pairs pay for the deep seven-frame pass. This
                # keeps full beginning/end evidence and excerpt confirmation
                # without decoding seven frames from every unrelated video.
                if path not in self._deep_video_fingerprint_cache:
                    self._deep_video_fingerprint_cache[path] = video_frame_phashes(path, samples=7)
                if other_path not in self._deep_video_fingerprint_cache:
                    self._deep_video_fingerprint_cache[other_path] = video_frame_phashes(
                        other_path,
                        samples=7,
                    )
                deep_fingerprint = self._deep_video_fingerprint_cache[path]
                other_deep_fingerprint = self._deep_video_fingerprint_cache[other_path]
                if deep_fingerprint is None or other_deep_fingerprint is None:
                    raise RuntimeError(
                        "A plausible video pair could not complete its confirmation pass. The "
                        "scan stopped instead of silently omitting that possible duplicate."
                    )
                if (
                    self.video_hashes_match(path, deep_fingerprint, other_path, other_deep_fingerprint)
                    and self.video_audio_tracks_match(path, other_path)
                ):
                    matches.append((other_path, other_deep_fingerprint, deep_fingerprint))
            if matches:
                for matched_path, matched_fingerprint, current_deep_fingerprint in matches:
                    live_group_id = group_id
                    group_id += 1
                    groups.append(
                        DupItem(
                            live_group_id,
                            "Similar video",
                            "High",
                            matched_path,
                            f"{len(matched_fingerprint.hashes)} aligned/ordered frame signatures",
                        )
                    )
                    groups.append(
                        DupItem(
                            live_group_id,
                            "Similar video",
                            "High",
                            path,
                            f"{len(current_deep_fingerprint.hashes)} aligned/ordered frame signatures",
                        )
                    )
                self.emit_partial(groups)
            video_hashes[path] = fingerprint
            for frame_index, hash_text in enumerate(fingerprint.hashes):
                video_hash_index.add(hash_text, (path, frame_index))

        self.map_paths_concurrently(
            video_files,
            "Video frames",
            62,
            18,
            lambda path: video_frame_phashes(path, samples=3),
            on_result=on_video_result,
            require_result=True,
        )
        self.emit_partial(groups, force=True)

        self.progress.emit("Checking similar audio tracks", 82)
        # Only complete audio files are peers. An audio extraction is not a safe
        # replacement for the video it came from, and allowing audio-video edges
        # can bridge unrelated videos that happen to share a soundtrack. Video
        # pairs already confirm their own audio tracks in the visual stage.
        audio_files = [
            p
            for p in files
            if p.suffix.lower() in AUDIO_EXTS
            and p.exists()
            and not self.path_was_intentionally_removed(p)
        ]
        audio_hashes: Dict[Path, str] = {}
        audio_hash_index = PerceptualHashBandIndex(12)

        def on_audio_result(path: Path, signature: object):
            nonlocal group_id
            if (
                not isinstance(signature, str)
                or self.path_was_intentionally_removed(path)
            ):
                return
            signature_text = str(signature)
            candidate_paths = {
                candidate_path
                for candidate_path, _hash_index in audio_hash_index.candidates(signature_text)
                if candidate_path.exists()
                and not self.path_was_intentionally_removed(candidate_path)
            }
            matches = [
                (other_path, audio_hashes[other_path])
                for other_path in candidate_paths
                if other_path in audio_hashes
                and not paths_are_already_exact_duplicates(path, other_path)
                for other_signature in [audio_hashes[other_path]]
                if self.audio_files_match(path, signature_text, other_path, other_signature)
            ]
            if matches:
                for matched_path, matched_signature in matches:
                    live_group_id = group_id
                    group_id += 1
                    groups.append(DupItem(live_group_id, "Similar audio", "Medium/High", matched_path, matched_signature[:16]))
                    groups.append(DupItem(live_group_id, "Similar audio", "Medium/High", path, signature_text[:16]))
                self.emit_partial(groups)
            audio_hashes[path] = signature_text
            audio_hash_index.add(signature_text, (path, 0))

        self.map_paths_concurrently(
            audio_files,
            "Audio",
            82,
            15,
            audio_signature,
            on_result=on_audio_result,
            require_result=True,
        )
        self.emit_partial(groups, force=True)

        groups = self.merge_duplicate_groups(groups)
        self.validate_duplicate_group_health(groups)
        self.attach_media_metadata(groups)
        groups = order_duplicate_items(groups)
        self.verify_scan_scope_unchanged(files)
        self.progress.emit(f"Done in {format_eta(time.time() - scan_started_at)}", 100)
        self.results_ready.emit(groups)

    def attach_media_metadata(self, groups: List[DupItem], emit_progress: bool = True):
        if not groups:
            return

        started_at = time.time()
        if emit_progress:
            self.progress.emit("Reading media metadata", 99)
        media_paths = list(
            dict.fromkeys(
                item.file
                for item in groups
                if (
                    item.file.exists()
                    and not self.path_was_intentionally_removed(item.file)
                    and (item.file.suffix.lower() in IMAGE_EXTS or is_media_path(item.file))
                )
            )
        )
        for path in media_paths:
            self.ensure_metadata_future(path)

        total = max(1, len(groups))
        for index, item in enumerate(groups, start=1):
            self.check_cancel()
            meta = self._metadata_cache.get(item.file)
            if meta is None and emit_progress:
                future = self._metadata_futures.get(item.file)
                if future is not None:
                    try:
                        meta = wait_for_scan_future(future)
                    except ScanCancelled:
                        raise
                    except Exception:
                        meta = MediaMeta()
                    self._metadata_cache[item.file] = meta
            if meta is None:
                try:
                    size = float(item.file.stat().st_size)
                except OSError:
                    size = 0.0
                item.quality_score = (0.0, 0.0, size, 0.0, 0.0)
                continue
            apply_duplicate_metadata(item, meta)
            if emit_progress and (index % 4 == 0 or index == total):
                self.progress.emit(
                    progress_text_with_eta("Metadata", index, total, started_at),
                    99,
                )


# ---------------------------------------------------------------------------
# File trees and window placement


class FinderWindowWatcher(PreviewProcessWorker):
    closed = Signal(str)

    def __init__(self, folder: Path):
        super().__init__()
        self.folder = folder
        self._stop_requested = False

    def stop(self):
        self._stop_requested = True
        self.cancel()

    def execute(self):
        target = normalized_folder_path(self.folder)
        seen_window = False
        started = time.time()

        while not self._stop_requested and not self.isInterruptionRequested():
            open_windows = set(finder_window_paths(run_process=self.run_subprocess))
            if target in open_windows:
                seen_window = True
            elif seen_window or time.time() - started > 10:
                self.closed.emit(str(self.folder))
                return
            self.msleep(900)


class FolderProgressDelegate(QStyledItemDelegate):
    """Paint cached folder size as a quiet, proportional hatched row."""

    def paint(self, painter: QPainter, option, index):
        super().paint(painter, option, index)


class TableScrollPolicy:
    """Keep wheel behavior identical across every file table."""

    def __init__(self, vertical_step: int = 12, horizontal_step: int = 24):
        self.vertical_step = max(1, int(vertical_step))
        self.horizontal_step = max(1, int(horizontal_step))
        self._views: List[weakref.ReferenceType] = []

    def _live_views(self) -> List[QAbstractItemView]:
        live_views: List[QAbstractItemView] = []
        live_references: List[weakref.ReferenceType] = []
        for reference in self._views:
            view = reference()
            if view is None:
                continue
            # A Python/Shiboken wrapper can outlive the native Qt table. A weak
            # reference therefore proves only that the wrapper exists, not that
            # calling QWidget methods is safe. Probe the native object and drop
            # stale wrappers before a global scroll-setting update reaches them.
            try:
                view.metaObject()
            except RuntimeError:
                continue
            live_views.append(view)
            live_references.append(reference)
        self._views = live_references
        return live_views

    def bind(self, view: QAbstractItemView):
        live_views = self._live_views()
        if not any(bound_view is view for bound_view in live_views):
            self._views.append(weakref.ref(view))
        self.apply(view)

    def apply(self, view: QAbstractItemView) -> bool:
        try:
            view.setVerticalScrollMode(QAbstractItemView.ScrollPerPixel)
            view.setHorizontalScrollMode(QAbstractItemView.ScrollPerPixel)
            view.verticalScrollBar().setSingleStep(self.vertical_step)
            view.horizontalScrollBar().setSingleStep(self.horizontal_step)
            return True
        except RuntimeError:
            # The native object can be destroyed between _live_views() and this
            # call while a dialog is closing. The next pass removes its wrapper.
            return False

    def configure(self, *, vertical_step: Optional[int] = None, horizontal_step: Optional[int] = None):
        if vertical_step is not None:
            self.vertical_step = max(1, int(vertical_step))
        if horizontal_step is not None:
            self.horizontal_step = max(1, int(horizontal_step))
        for view in self._live_views():
            self.apply(view)

    def set_horizontal_step(self, step: int):
        self.configure(horizontal_step=step)

    def horizontal_wheel_distance(self, event) -> int:
        """Return one normalized pixel distance for every bound table."""
        pixel_delta = event.pixelDelta()
        angle_delta = event.angleDelta()
        shift_scroll = bool(event.modifiers() & Qt.ShiftModifier)
        delta = 0.0

        if shift_scroll:
            if not pixel_delta.isNull() and pixel_delta.y():
                delta = float(pixel_delta.y())
            elif angle_delta.y():
                delta = (float(angle_delta.y()) / 120.0) * self.horizontal_step
        elif not pixel_delta.isNull() and pixel_delta.x() and abs(pixel_delta.x()) >= abs(pixel_delta.y()):
            delta = float(pixel_delta.x())
        elif angle_delta.x() and abs(angle_delta.x()) >= abs(angle_delta.y()):
            delta = (float(angle_delta.x()) / 120.0) * self.horizontal_step
        return round(delta)

    def handle_horizontal_wheel(self, view: QAbstractItemView, event) -> bool:
        delta = self.horizontal_wheel_distance(event)
        if not delta:
            return False
        scrollbar = view.horizontalScrollBar()
        if scrollbar.minimum() == scrollbar.maximum():
            return False
        scrollbar.setValue(scrollbar.value() - delta)
        event.accept()
        return True


TABLE_SCROLL_POLICY = TableScrollPolicy()


class FileTreeWidget(QTreeWidget):
    deletePressed = Signal()
    undoPressed = Signal()
    redoPressed = Signal()
    openPressed = Signal()
    playPausePressed = Signal()
    previewPressed = Signal()
    renamePressed = Signal()
    reviewStepPressed = Signal(int)
    blankClicked = Signal()
    filesDropped = Signal(list)
    disclosurePressed = Signal(object)

    def __init__(self, parent=None):
        super().__init__(parent)
        self.disclosure_click_active = False
        self.disclosure_press_index: Optional[QPersistentModelIndex] = None
        self.disclosure_press_scroll: Optional[int] = None
        self.preview_navigation_active = False
        self.folder_drop_enabled = False
        self.file_drag_enabled = False
        self.return_renames = False
        self.setTextElideMode(Qt.ElideMiddle)
        self.setWordWrap(False)
        self.setUniformRowHeights(True)
        self.setAnimated(False)
        TABLE_SCROLL_POLICY.bind(self)

    def wheelEvent(self, event):
        if TABLE_SCROLL_POLICY.handle_horizontal_wheel(self, event):
            return
        super().wheelEvent(event)

    def drawBranches(self, painter: QPainter, rect: QRect, index: QModelIndex):
        # Rows already render their own disclosure marker in column zero. Qt's
        # native branch glyph created a second chevron and a conflicting hit area.
        return

    def drawRow(self, painter: QPainter, option, index: QModelIndex):
        super().drawRow(painter, option, index)
        try:
            ratio = index.siblingAtColumn(0).data(FOLDER_PROGRESS_ROLE)
            if ratio is None:
                return
            ratio = max(0.0, min(1.0, float(ratio)))
            if ratio <= 0.0:
                return
            row_rect = QRect(option.rect)
            row_rect.setLeft(0)
            row_rect.setWidth(max(1, int(self.viewport().width() * ratio)))
            painter.save()
            painter.fillRect(row_rect, QBrush(QColor(139, 149, 184, 92), Qt.BDiagPattern))
            painter.setPen(QPen(QColor(177, 186, 220, 150), 1))
            painter.drawLine(row_rect.topRight(), row_rect.bottomRight())
            painter.restore()
        except (RuntimeError, TypeError, ValueError):
            return

    def setFolderDropEnabled(self, enabled: bool):
        self.folder_drop_enabled = enabled
        self.setAcceptDrops(enabled)
        self.viewport().setAcceptDrops(enabled)

    def setFileDragEnabled(self, enabled: bool):
        self.file_drag_enabled = enabled
        self.setDragEnabled(enabled)
        if enabled:
            self.setDragDropMode(QAbstractItemView.DragDrop)
            self.setDefaultDropAction(Qt.MoveAction)

    def has_command_modifier(self, modifiers) -> bool:
        # In Qt raw key events on macOS, the physical Command key is ControlModifier.
        return bool(modifiers & Qt.ControlModifier)

    def keyPressEvent(self, event):
        key = event.key()
        modifiers = event.modifiers()
        plain_navigation = not (modifiers & (Qt.ShiftModifier | Qt.ControlModifier | Qt.AltModifier | Qt.MetaModifier))

        if key in (Qt.Key_Return, Qt.Key_Enter):
            if self.return_renames:
                self.renamePressed.emit()
            else:
                self.playPausePressed.emit()
            event.accept()
            return

        if key == Qt.Key_Space:
            current = self.currentItem()
            debug_log(
                "input",
                "Space pressed in file table",
                force=True,
                selected_count=len(self.selectedItems()),
                row_kind=current.data(0, Qt.UserRole) if current is not None else "none",
            )
            self.previewPressed.emit()
            event.accept()
            return

        if key in (Qt.Key_Up, Qt.Key_Down) and self.preview_navigation_active and plain_navigation:
            self.reviewStepPressed.emit(-1 if key == Qt.Key_Up else 1)
            event.accept()
            return

        if key in (Qt.Key_Delete, Qt.Key_Backspace) and self.has_command_modifier(modifiers):
            self.deletePressed.emit()
            event.accept()
            return

        if key == Qt.Key_Z and self.has_command_modifier(modifiers):
            if modifiers & Qt.ShiftModifier:
                self.redoPressed.emit()
            else:
                self.undoPressed.emit()
            event.accept()
            return

        if key == Qt.Key_Y and self.has_command_modifier(modifiers):
            self.redoPressed.emit()
            event.accept()
            return

        super().keyPressEvent(event)

    def disclosure_item_at(self, pos: QPoint) -> Optional[QTreeWidgetItem]:
        item = self.itemAt(pos)
        # Qt reports no item for part of its hidden native branch gutter. Probe
        # the same y-coordinate inside the Name column so every pixel to the
        # left of our painted triangle resolves to the row the user can see.
        if item is None and 0 <= pos.y() < self.viewport().height():
            try:
                header = self.header()
                name_left = header.sectionViewportPosition(0)
                name_width = header.sectionSize(0)
                probe_x = max(0, min(self.viewport().width() - 1, name_left + name_width - 3))
                index = self.indexAt(QPoint(probe_x, pos.y()))
                if index.isValid():
                    item = self.itemFromIndex(index)
            except (AttributeError, RuntimeError):
                item = None
        return item

    @staticmethod
    def is_disclosure_item(item: Optional[QTreeWidgetItem]) -> bool:
        if item is None:
            return False
        disclosure_kind = item.data(0, Qt.UserRole) if item is not None else None
        alternate_kind = item.data(0, Qt.UserRole + 1) if item is not None else None
        return (
            disclosure_kind
            in {
                "folder",
                "folder-child",
                "group",
                "subgroup",
                "media-header",
                "media-ext-header",
            }
            or alternate_kind in {"reason", "folder_group"}
        )

    def begin_disclosure_click(self, event, pos: QPoint, item: Optional[QTreeWidgetItem]) -> bool:
        if event.button() != Qt.LeftButton or not self.is_disclosure_item(item):
            return False
        rect = self.visualItemRect(item)
        # Only the triangle and its leading gutter toggle expansion. The action
        # belongs to the matching release, so rapid clicks cannot leave queued
        # press toggles racing against Qt's double-click handling.
        if pos.x() > rect.left() + 28:
            return False

        self.disclosure_click_active = True
        self.disclosure_press_index = QPersistentModelIndex(self.indexFromItem(item, 0))
        self.disclosure_press_scroll = self.horizontalScrollBar().value()
        modifiers = event.modifiers()
        if not (modifiers & (Qt.ShiftModifier | Qt.ControlModifier | Qt.MetaModifier)):
            self.clearSelection()
        item.setSelected(True)
        self.setCurrentItem(item)
        self.horizontalScrollBar().setValue(self.disclosure_press_scroll)
        event.accept()
        return True

    def reset_disclosure_click(self):
        self.disclosure_click_active = False
        self.disclosure_press_index = None
        self.disclosure_press_scroll = None

    def mousePressEvent(self, event):
        pos = event.position().toPoint() if hasattr(event, "position") else event.pos()
        item = self.disclosure_item_at(pos)
        if self.begin_disclosure_click(event, pos, item):
            return
        if event.button() == Qt.LeftButton and item is None:
            self.clearSelection()
            try:
                self.selectionModel().clearCurrentIndex()
            except Exception:
                pass
            self.blankClicked.emit()
            event.accept()
            return
        super().mousePressEvent(event)

    def mouseDoubleClickEvent(self, event):
        pos = event.position().toPoint() if hasattr(event, "position") else event.pos()
        item = self.disclosure_item_at(pos)
        if self.begin_disclosure_click(event, pos, item):
            return
        super().mouseDoubleClickEvent(event)

    def mouseReleaseEvent(self, event):
        if self.disclosure_click_active and event.button() == Qt.LeftButton:
            pos = event.position().toPoint() if hasattr(event, "position") else event.pos()
            release_item = self.disclosure_item_at(pos)
            persistent = self.disclosure_press_index
            horizontal_scroll = self.disclosure_press_scroll
            same_item = False
            if persistent is not None and persistent.isValid() and release_item is not None:
                release_index = self.indexFromItem(release_item, 0)
                release_rect = self.visualItemRect(release_item)
                same_item = (
                    release_index == QModelIndex(persistent)
                    and pos.x() <= release_rect.left() + 28
                )
            self.reset_disclosure_click()
            if same_item and persistent is not None:
                # Expansion can invalidate item wrappers while Qt is dispatching
                # mouse events. Resolve the persistent index on the next event-loop
                # turn, after this complete click has finished.
                QTimer.singleShot(
                    0,
                    lambda index=persistent, scroll=horizontal_scroll:
                        self.emit_deferred_disclosure(index, scroll),
                )
            event.accept()
            return
        self.reset_disclosure_click()
        super().mouseReleaseEvent(event)

    def emit_deferred_disclosure(self, persistent: QPersistentModelIndex, horizontal_scroll: Optional[int] = None):
        if not persistent.isValid():
            return
        item = self.itemFromIndex(QModelIndex(persistent))
        if item is not None:
            self.disclosurePressed.emit(item)
        if horizontal_scroll is not None:
            self.horizontalScrollBar().setValue(horizontal_scroll)

    def supportedDragActions(self):
        return Qt.MoveAction | Qt.CopyAction

    def mimeData(self, items: List[QTreeWidgetItem]):
        mime = QMimeData()
        if not self.file_drag_enabled:
            return mime
        urls = []
        seen = set()
        for item in items:
            path_text = item.data(0, Qt.UserRole + 1)
            if not path_text:
                continue
            path = Path(path_text)
            if path in seen or not path.exists():
                continue
            urls.append(QUrl.fromLocalFile(str(path)))
            seen.add(path)
        if urls:
            mime.setUrls(urls)
        return mime

    def dragEnterEvent(self, event: QDragEnterEvent):
        if not self.folder_drop_enabled or not event.mimeData().hasUrls():
            event.ignore()
            return
        if any(url.isLocalFile() for url in event.mimeData().urls()):
            event.acceptProposedAction()
            return
        event.ignore()

    def dragMoveEvent(self, event):
        if self.folder_drop_enabled and event.mimeData().hasUrls():
            event.acceptProposedAction()
            return
        event.ignore()

    def dropEvent(self, event: QDropEvent):
        if not self.folder_drop_enabled:
            event.ignore()
            return
        paths = [Path(url.toLocalFile()) for url in event.mimeData().urls() if url.isLocalFile()]
        if paths:
            self.filesDropped.emit(paths)
            event.acceptProposedAction()
            return
        event.ignore()


def restore_tree_header_state(tree: QTreeWidget, key: str):
    header = tree.header()
    settings = app_settings()
    state = settings.value(f"tables/{key}/header")
    if state:
        try:
            header.restoreState(state)
        except Exception:
            pass


def save_tree_header_state(tree: QTreeWidget, key: str):
    try:
        app_settings().setValue(f"tables/{key}/header", tree.header().saveState())
    except Exception:
        pass


def connect_tree_header_persistence(tree: QTreeWidget, key: str):
    header = tree.header()
    header.sectionResized.connect(lambda *_args: save_tree_header_state(tree, key))
    header.sectionMoved.connect(lambda *_args: save_tree_header_state(tree, key))
    header.sortIndicatorChanged.connect(lambda *_args: save_tree_header_state(tree, key))


def window_geometry_settings(widget: QWidget) -> QSettings:
    """Allow an embedding app to keep its own geometry namespace."""
    current = widget
    seen: set[int] = set()
    while current is not None and id(current) not in seen:
        seen.add(id(current))
        override = getattr(current, "_folder_manager_geometry_settings", None)
        if isinstance(override, QSettings):
            return override
        try:
            current = current.parentWidget()
        except (AttributeError, RuntimeError):
            current = None
    return app_settings()


def screen_identity(screen) -> Tuple[str, str]:
    if screen is None:
        return "", ""
    try:
        name = str(screen.name() or "")
    except Exception:
        name = ""
    try:
        serial = str(screen.serialNumber() or "")
    except Exception:
        serial = ""
    return name, serial


def capture_window_placement(widget: QWidget, rect: Optional[QRect] = None) -> Dict[str, object]:
    """Capture a normal rectangle together with the display that owns it."""
    target = QRect(rect) if isinstance(rect, QRect) else QRect(widget.geometry())
    screen = None
    try:
        screen = QApplication.screenAt(target.center())
    except Exception:
        pass
    if screen is None:
        try:
            screen = widget.screen()
        except Exception:
            pass
    available = QRect(screen.availableGeometry()) if screen is not None else QRect()
    name, serial = screen_identity(screen)
    return {
        "rect": QRect(target),
        "available": available,
        "screen_name": name,
        "screen_serial": serial,
    }


def saved_window_placement(widget: QWidget, key: str) -> Optional[Dict[str, object]]:
    settings = window_geometry_settings(widget)
    rect = settings.value(f"windows/{key}/rect")
    if not isinstance(rect, QRect) or not rect.isValid():
        return None
    available = settings.value(f"windows/{key}/screen_available")
    return {
        "rect": QRect(rect),
        "available": QRect(available) if isinstance(available, QRect) else QRect(),
        "screen_name": str(settings.value(f"windows/{key}/screen_name", "") or ""),
        "screen_serial": str(settings.value(f"windows/{key}/screen_serial", "") or ""),
    }


def persist_window_placement(widget: QWidget, key: str, rect: Optional[QRect] = None):
    placement = capture_window_placement(widget, rect)
    settings = window_geometry_settings(widget)
    settings.setValue(f"windows/{key}/rect", placement["rect"])
    settings.setValue(f"windows/{key}/screen_available", placement["available"])
    settings.setValue(f"windows/{key}/screen_name", placement["screen_name"])
    settings.setValue(f"windows/{key}/screen_serial", placement["screen_serial"])
    return placement


def screen_for_window_placement(widget: QWidget, placement: Optional[Dict[str, object]]):
    screens = QApplication.screens()
    if not screens:
        return None
    placement = placement or {}
    wanted_serial = str(placement.get("screen_serial", "") or "")
    wanted_name = str(placement.get("screen_name", "") or "")
    if wanted_serial:
        for screen in screens:
            if screen_identity(screen)[1] == wanted_serial:
                return screen
    if wanted_name:
        for screen in screens:
            if screen_identity(screen)[0] == wanted_name:
                return screen
    rect = placement.get("rect")
    if isinstance(rect, QRect) and rect.isValid():
        try:
            screen = QApplication.screenAt(rect.center())
            if screen is not None:
                return screen
        except Exception:
            pass
    try:
        screen = widget.screen()
        if screen is not None:
            return screen
    except Exception:
        pass
    return QApplication.primaryScreen() or screens[0]


def restore_rect_for_window_placement(
    widget: QWidget,
    placement: Optional[Dict[str, object]],
    fallback: Optional[QRect] = None,
) -> QRect:
    """Map a saved rectangle to its original display and keep it reachable."""
    placement = placement or {}
    saved = placement.get("rect")
    rect = QRect(saved) if isinstance(saved, QRect) and saved.isValid() else QRect(fallback or QRect())
    if not rect.isValid():
        return rect
    screen = screen_for_window_placement(widget, placement)
    if screen is None:
        return rect
    target_available = QRect(screen.availableGeometry())
    saved_available = placement.get("available")
    if isinstance(saved_available, QRect) and saved_available.isValid():
        # Display coordinates can change after docking/undocking. Preserve the
        # window's offset on that display instead of restoring to another one.
        if saved_available != target_available:
            rect.moveTo(
                target_available.left() + rect.left() - saved_available.left(),
                target_available.top() + rect.top() - saved_available.top(),
            )
    width = min(max(1, rect.width()), max(1, target_available.width()))
    height = min(max(1, rect.height()), max(1, target_available.height()))
    left = min(max(rect.left(), target_available.left()), target_available.right() - width + 1)
    top = min(max(rect.top(), target_available.top()), target_available.bottom() - height + 1)
    return QRect(left, top, width, height)


def top_level_window_for(widget: Optional[QWidget]) -> Optional[QWidget]:
    """Resolve a tab/panel owner to the real top-level native window."""
    if widget is None:
        return None
    try:
        candidate = widget.window()
        if isinstance(candidate, QWidget) and candidate.isWindow():
            return candidate
    except (AttributeError, RuntimeError):
        pass
    try:
        return widget if widget.isWindow() else None
    except (AttributeError, RuntimeError):
        return None


def temporarily_attach_window_to_owner_space(
    widget: QWidget,
    owner: Optional[QWidget],
    duration_ms: int = 1600,
) -> bool:
    """Use a transient-parent bridge without ever pushing the child behind its owner.

    Older builds activated/raised the owner first. On macOS that produced the visible
    200-300 ms flash where Preview/Debug/scanners disappeared behind the main window
    after leaving fullscreen. The transient relationship itself is enough to give
    Cocoa the Space affinity; keep the auxiliary window frontmost throughout.
    """
    if sys.platform != "darwin":
        return False
    owner_window = top_level_window_for(owner)
    if owner_window is None or owner_window is widget:
        return False
    try:
        widget.winId()
        owner_window.winId()
        target_handle = widget.windowHandle()
        owner_handle = owner_window.windowHandle()
        if target_handle is None or owner_handle is None:
            return False
        generation = int(getattr(widget, "_folder_manager_transient_generation", 0)) + 1
        setattr(widget, "_folder_manager_transient_generation", generation)
        original = target_handle.transientParent()
        target_handle.setTransientParent(owner_handle)
        try:
            native = macos_native_window(widget)
            if native is not None:
                native.makeKeyAndOrderFront_(None)
        except Exception:
            pass
        widget.raise_()
        widget.activateWindow()

        def release_transient_parent():
            try:
                if generation != int(getattr(widget, "_folder_manager_transient_generation", 0)):
                    return
                handle = widget.windowHandle()
                if handle is not None:
                    handle.setTransientParent(original)
            except (AttributeError, RuntimeError):
                pass

        QTimer.singleShot(max(500, int(duration_ms)), release_transient_parent)
        return True
    except (AttributeError, RuntimeError):
        return False


def prepare_macos_window_restore_context(widget: QWidget, owner: Optional[QWidget] = None) -> int:
    """Keep an auxiliary window on its originating Space without front-order flicker.

    The previous implementation briefly activated the main owner and waited 300 ms
    before bringing the auxiliary window forward again. That was the exact visible
    hide-behind-main-window blink on fullscreen exit. We now establish Space affinity
    while leaving the auxiliary window key/front for the whole transition.
    """
    if sys.platform != "darwin":
        return 0
    owner = top_level_window_for(owner)
    temporarily_attach_window_to_owner_space(widget, owner)
    try:
        from AppKit import (
            NSApplication,
            NSWindowCollectionBehaviorCanJoinAllSpaces,
            NSWindowCollectionBehaviorMoveToActiveSpace,
        )

        window = macos_native_window(widget)
        if window is not None:
            original = int(window.collectionBehavior())
            setattr(widget, "_folder_manager_original_collection_behavior", original)
            behavior = (original & ~int(NSWindowCollectionBehaviorCanJoinAllSpaces)) | int(
                NSWindowCollectionBehaviorMoveToActiveSpace
            )
            window.setCollectionBehavior_(behavior)
            NSApplication.sharedApplication().activateIgnoringOtherApps_(True)
            window.makeKeyAndOrderFront_(None)

            generation = int(getattr(widget, "_folder_manager_restore_front_generation", 0)) + 1
            setattr(widget, "_folder_manager_restore_front_generation", generation)

            def restore_behavior():
                try:
                    if generation != int(getattr(widget, "_folder_manager_restore_front_generation", 0)):
                        return
                    native = macos_native_window(widget)
                    saved = getattr(widget, "_folder_manager_original_collection_behavior", None)
                    if native is not None and saved is not None:
                        native.setCollectionBehavior_(saved)
                    setattr(widget, "_folder_manager_original_collection_behavior", None)
                except (AttributeError, RuntimeError):
                    pass

            QTimer.singleShot(1400, restore_behavior)
    except ModuleNotFoundError:
        pass
    except Exception as exc:
        if not bool(getattr(widget, "_folder_manager_space_restore_error_logged", False)):
            setattr(widget, "_folder_manager_space_restore_error_logged", True)
            debug_log(
                "window",
                "native Space assist unavailable; Qt owner bridge retained",
                force=True,
                widget=widget.__class__.__name__,
                error=type(exc).__name__,
            )
    try:
        widget.raise_()
        widget.activateWindow()
        widget.setFocus(Qt.ActiveWindowFocusReason)
    except (AttributeError, RuntimeError):
        pass
    return 0


def restore_window_geometry(widget: QWidget, key: str):
    settings = window_geometry_settings(widget)
    geometry = settings.value(f"windows/{key}/geometry")
    if geometry:
        try:
            widget.restoreGeometry(geometry)
            placement = saved_window_placement(widget, key)
            target = restore_rect_for_window_placement(widget, placement, QRect(widget.geometry()))
            if target.isValid():
                widget.setGeometry(target)
            widget.setProperty("folderManagerStableGeometry", geometry)
            widget.setProperty("folderManagerStableRect", QRect(widget.geometry()))
            setattr(widget, "_folder_manager_last_windowed_placement", capture_window_placement(widget))
        except Exception:
            pass


def window_geometry_is_stable(widget: QWidget) -> bool:
    """Ignore synthetic moves generated while macOS changes Spaces/window state."""
    try:
        if bool(getattr(widget, "_folder_manager_geometry_restore_pending", False)):
            return False
        if not widget.isVisible() or not widget.isActiveWindow() or not application_is_active():
            return False
        state = widget.windowState()
        unstable = Qt.WindowMinimized | Qt.WindowMaximized | Qt.WindowFullScreen
        return not bool(state & unstable)
    except (AttributeError, RuntimeError):
        return False


def save_window_geometry(widget: QWidget, key: str, *, force: bool = False):
    if not force and not window_geometry_is_stable(widget):
        return
    try:
        geometry = widget.saveGeometry()
        window_geometry_settings(widget).setValue(f"windows/{key}/geometry", geometry)
        placement = persist_window_placement(widget, key)
        widget.setProperty("folderManagerStableGeometry", geometry)
        widget.setProperty("folderManagerStableRect", QRect(widget.geometry()))
        setattr(widget, "_folder_manager_last_windowed_placement", placement)
    except Exception:
        pass


def window_geometry_looks_like_macos_zoom(widget: QWidget, geometry: QRect) -> bool:
    """Match the preview window's screen-sized-frame rejection rule."""
    if sys.platform != "darwin" or not geometry.isValid():
        return False
    screen = widget.screen()
    if screen is None:
        return False
    available = screen.availableGeometry()
    if not available.isValid() or available.width() <= 0 or available.height() <= 0:
        return False
    fills_width = geometry.width() >= int(available.width() * 0.96)
    fills_height = geometry.height() >= int(available.height() * 0.88)
    aligned_left = abs(geometry.left() - available.left()) <= 24
    aligned_top = abs(geometry.top() - available.top()) <= 80
    return fills_width and fills_height and aligned_left and aligned_top


def configure_settled_window_geometry(widget: QWidget, key: str, default_size: QSize):
    """Give an ordinary dialog the preview window's resize/restore discipline."""
    setattr(widget, "_folder_manager_geometry_key", key)
    restore_window_geometry(widget, key)
    geometry = QRect(widget.geometry())
    repaired = False
    if not geometry.isValid() or window_geometry_looks_like_macos_zoom(widget, geometry):
        screen = widget.screen()
        available = screen.availableGeometry() if screen is not None else QRect()
        width = max(640, int(default_size.width()))
        height = max(420, int(default_size.height()))
        if available.isValid():
            width = min(width, max(640, available.width() - 80))
            height = min(height, max(420, available.height() - 80))
            left = available.left() + max(0, (available.width() - width) // 2)
            top = available.top() + max(0, (available.height() - height) // 2)
            geometry = QRect(left, top, width, height)
            widget.setGeometry(geometry)
        else:
            widget.resize(width, height)
            geometry = QRect(widget.geometry())
        repaired = True

    setattr(widget, "_folder_manager_last_windowed_geometry", QRect(geometry))
    setattr(widget, "_folder_manager_opening_windowed_geometry", QRect(geometry))
    placement = capture_window_placement(widget, geometry)
    setattr(widget, "_folder_manager_last_windowed_placement", placement)
    setattr(widget, "_folder_manager_opening_windowed_placement", placement)
    widget.setProperty("folderManagerStableRect", QRect(geometry))
    widget.setProperty("folderManagerStableGeometry", widget.saveGeometry())
    timer = QTimer(widget)
    timer.setSingleShot(True)
    timer.setInterval(300)
    timer.timeout.connect(lambda: remember_settled_window_geometry(widget, key))
    setattr(widget, "geometry_save_timer", timer)
    if repaired:
        # Replace geometry polluted by an earlier fullscreen transition now, so
        # reopening the scanner cannot resurrect the desktop-sized rectangle.
        window_geometry_settings(widget).setValue(f"windows/{key}/geometry", widget.saveGeometry())
        persist_window_placement(widget, key, geometry)


def schedule_settled_window_geometry_remember(widget: QWidget):
    """Debounce resize/move events until the final native state is observable."""
    timer = getattr(widget, "geometry_save_timer", None)
    if timer is None:
        return
    try:
        state = widget.windowState()
        if (
            widget.isFullScreen()
            or bool(state & Qt.WindowMaximized)
            or bool(getattr(widget, "_folder_manager_geometry_restore_pending", False))
            or bool(getattr(widget, "_folder_manager_fullscreen_cycle", False))
        ):
            timer.stop()
            return
        timer.start()
    except RuntimeError:
        timer.stop()


def remember_settled_window_geometry(widget: QWidget, key: str):
    """Persist only a genuine, settled normal-window rectangle."""
    try:
        state = widget.windowState()
        if (
            widget.isFullScreen()
            or bool(state & Qt.WindowMaximized)
            or bool(getattr(widget, "_folder_manager_geometry_restore_pending", False))
            or bool(getattr(widget, "_folder_manager_fullscreen_cycle", False))
        ):
            return
        geometry = QRect(widget.geometry())
        if (
            not geometry.isValid()
            or geometry.width() <= 0
            or geometry.height() <= 0
            or window_geometry_looks_like_macos_zoom(widget, geometry)
        ):
            return
        previous = getattr(widget, "_folder_manager_last_windowed_geometry", None)
        setattr(widget, "_folder_manager_last_windowed_geometry", QRect(geometry))
        placement = capture_window_placement(widget, geometry)
        setattr(widget, "_folder_manager_last_windowed_placement", placement)
        widget.setProperty("folderManagerStableRect", QRect(geometry))
        widget.setProperty("folderManagerStableGeometry", widget.saveGeometry())
        window_geometry_settings(widget).setValue(f"windows/{key}/geometry", widget.saveGeometry())
        persist_window_placement(widget, key, geometry)
        if previous != geometry:
            debug_log(
                "window",
                "scanner window geometry settled",
                widget=widget.__class__.__name__,
                x=geometry.x(),
                y=geometry.y(),
                width=geometry.width(),
                height=geometry.height(),
            )
    except RuntimeError:
        return


def capture_standard_window_geometry(widget: QWidget, key: str):
    """Capture the normal window rectangle before Cocoa starts fullscreen."""
    if bool(getattr(widget, "_folder_manager_fullscreen_cycle", False)):
        return
    timer = getattr(widget, "geometry_save_timer", None)
    if timer is not None:
        timer.stop()
    normal = None
    try:
        normal = QRect(widget.normalGeometry())
    except Exception:
        pass
    current = QRect(widget.geometry())
    state = widget.windowState()
    current_is_normal = not bool(state & (Qt.WindowFullScreen | Qt.WindowMaximized))
    candidates = (
        current if current_is_normal else None,
        normal,
        getattr(widget, "_folder_manager_last_windowed_geometry", None),
        getattr(widget, "_folder_manager_opening_windowed_geometry", None),
        widget.property("folderManagerStableRect"),
        current,
    )
    rect = None
    for candidate in candidates:
        if (
            isinstance(candidate, QRect)
            and candidate.isValid()
            and candidate.width() > 0
            and candidate.height() > 0
            and not window_geometry_looks_like_macos_zoom(widget, candidate)
        ):
            rect = QRect(candidate)
            break
    if rect is None:
        try:
            rect = QRect(widget.geometry())
        except Exception:
            return
    setattr(widget, "_folder_manager_pre_fullscreen_geometry", None)
    setattr(widget, "_folder_manager_pre_fullscreen_rect", QRect(rect))
    placement = capture_window_placement(widget, rect)
    setattr(widget, "_folder_manager_pre_fullscreen_placement", placement)
    setattr(widget, "_folder_manager_fullscreen_cycle", True)
    debug_log(
        "window",
        "captured normal geometry before fullscreen",
        force=True,
        widget=widget.__class__.__name__,
        x=rect.x(),
        y=rect.y(),
        width=rect.width(),
        height=rect.height(),
    )


def restore_standard_window_geometry(widget: QWidget, key: str, generation: int):
    """Verify a native fullscreen exit before restoring its frozen rectangle."""
    if generation != int(getattr(widget, "_folder_manager_restore_generation", 0)):
        return
    try:
        now = time.monotonic()
        state = widget.windowState()
        # Never let a delayed fullscreen-restore callback touch a dialog that has
        # already been closed/hidden. Calling setGeometry() on a hidden Qt top-level
        # can cause Cocoa to recreate/order-in an empty NSWindow shell.
        if not widget.isVisible():
            finish_standard_window_restore(widget, generation)
            return
        placement = getattr(widget, "_folder_manager_pre_fullscreen_placement", None)
        target = getattr(widget, "_folder_manager_pre_fullscreen_rect", None)
        if not isinstance(target, QRect) or not target.isValid():
            target = getattr(widget, "_folder_manager_last_windowed_geometry", None)
            placement = getattr(widget, "_folder_manager_last_windowed_placement", placement)
        if not isinstance(target, QRect) or not target.isValid():
            finish_standard_window_restore(widget, generation)
            return
        target = restore_rect_for_window_placement(widget, placement, QRect(target))
        wrong_state = bool(state & (Qt.WindowFullScreen | Qt.WindowMaximized))
        started_at = float(getattr(widget, "_folder_manager_restore_started_at", now))
        deadline = float(getattr(widget, "_folder_manager_restore_deadline", now))
        if wrong_state:
            if (
                not bool(getattr(widget, "_folder_manager_restore_fallback_issued", False))
                and now - started_at >= 3.0
            ):
                setattr(widget, "_folder_manager_restore_fallback_issued", True)
                widget.showNormal()
            if now < deadline:
                QTimer.singleShot(180, lambda: restore_standard_window_geometry(widget, key, generation))
                return

        last_state_change = float(
            getattr(widget, "_folder_manager_restore_last_state_change", started_at)
        )
        if not wrong_state and now - last_state_change < 0.55:
            QTimer.singleShot(180, lambda: restore_standard_window_geometry(widget, key, generation))
            return

        if not bool(getattr(widget, "_folder_manager_restore_context_prepared", False)):
            setattr(widget, "_folder_manager_restore_context_prepared", True)
            owner = getattr(widget, "owner_window", None)
            if owner is None:
                try:
                    owner = widget.parentWidget()
                except (AttributeError, RuntimeError):
                    owner = None
            delay = prepare_macos_window_restore_context(
                widget,
                owner,
            )
            if delay:
                QTimer.singleShot(delay, lambda: restore_standard_window_geometry(widget, key, generation))
                return

        actual = QRect(widget.geometry())
        wrong_geometry = any(
            (
                abs(actual.x() - target.x()) > 3,
                abs(actual.y() - target.y()) > 3,
                abs(actual.width() - target.width()) > 3,
                abs(actual.height() - target.height()) > 3,
            )
        )
        if not wrong_state and wrong_geometry:
            widget.setGeometry(QRect(target))
            setattr(widget, "_folder_manager_last_windowed_geometry", QRect(target))
            setattr(widget, "_folder_manager_restore_stable_checks", 0)
            QTimer.singleShot(220, lambda: restore_standard_window_geometry(widget, key, generation))
            return

        stable_checks = int(getattr(widget, "_folder_manager_restore_stable_checks", 0)) + 1
        setattr(widget, "_folder_manager_restore_stable_checks", stable_checks)
        if not wrong_state and not wrong_geometry and stable_checks < 3:
            QTimer.singleShot(180, lambda: restore_standard_window_geometry(widget, key, generation))
            return
        if wrong_state or wrong_geometry:
            debug_log(
                "window",
                "scanner window restore did not settle before deadline",
                force=True,
                widget=widget.__class__.__name__,
            )
            finish_standard_window_restore(widget, generation)
            return

        setattr(widget, "_folder_manager_last_windowed_geometry", QRect(target))
        placement = capture_window_placement(widget, target)
        setattr(widget, "_folder_manager_last_windowed_placement", placement)
        widget.setProperty("folderManagerStableRect", QRect(target))
        widget.setProperty("folderManagerStableGeometry", widget.saveGeometry())
        window_geometry_settings(widget).setValue(f"windows/{key}/geometry", widget.saveGeometry())
        persist_window_placement(widget, key, target)
        debug_log(
            "window",
            "restored normal geometry after fullscreen",
            force=True,
            widget=widget.__class__.__name__,
            x=target.x(),
            y=target.y(),
            width=target.width(),
            height=target.height(),
        )
        finish_standard_window_restore(widget, generation)
    except RuntimeError:
        return


def finish_standard_window_restore(widget: QWidget, generation: int):
    if generation != int(getattr(widget, "_folder_manager_restore_generation", 0)):
        return
    setattr(widget, "_folder_manager_geometry_restore_pending", False)
    setattr(widget, "_folder_manager_fullscreen_cycle", False)
    setattr(widget, "_folder_manager_pre_fullscreen_rect", None)
    setattr(widget, "_folder_manager_pre_fullscreen_placement", None)


def schedule_standard_window_restore(widget: QWidget, key: str):
    generation = int(getattr(widget, "_folder_manager_restore_generation", 0)) + 1
    setattr(widget, "_folder_manager_restore_generation", generation)
    setattr(widget, "_folder_manager_geometry_restore_pending", True)
    now = time.monotonic()
    setattr(widget, "_folder_manager_restore_started_at", now)
    setattr(widget, "_folder_manager_restore_last_state_change", now)
    setattr(widget, "_folder_manager_restore_deadline", now + 8.0)
    setattr(widget, "_folder_manager_restore_fallback_issued", False)
    setattr(widget, "_folder_manager_restore_stable_checks", 0)
    setattr(widget, "_folder_manager_restore_context_prepared", False)
    # As in Preview, Cocoa owns the Space transition. Wait for its state and
    # frame animation to finish before applying the frozen windowed rectangle.
    QTimer.singleShot(180, lambda: restore_standard_window_geometry(widget, key, generation))


def track_standard_fullscreen_change(widget: QWidget, event, key: str):
    if event.type() != QEvent.WindowStateChange:
        return
    try:
        old_state = event.oldState()
    except Exception:
        old_state = Qt.WindowStates()
    new_state = widget.windowState()
    setattr(widget, "_folder_manager_restore_last_state_change", time.monotonic())
    old_expanded = bool(
        getattr(
            widget,
            "_folder_manager_was_expanded",
            bool(old_state & (Qt.WindowFullScreen | Qt.WindowMaximized)),
        )
    )
    new_expanded = bool(new_state & (Qt.WindowFullScreen | Qt.WindowMaximized))
    if not old_expanded and new_expanded:
        capture_standard_window_geometry(widget, key)
    elif old_expanded and not new_expanded:
        # A close requested from native fullscreen owns this transition. Its
        # close poll restores the frozen frame and then orders the NSWindow out;
        # starting the ordinary restore loop at the same time can resurrect an
        # already-closing Cocoa shell with an empty white content view.
        if not bool(getattr(widget, "_folder_manager_close_after_expanded_exit", False)):
            schedule_standard_window_restore(widget, key)
    setattr(widget, "_folder_manager_was_expanded", new_expanded)
    setattr(widget, "_folder_manager_was_fullscreen", bool(new_state & Qt.WindowFullScreen))


def defer_close_until_windowed(widget: QWidget, event, key: str) -> bool:
    """Exit native fullscreen completely before allowing Qt to tear down UI.

    Cocoa moves a fullscreen NSWindow between Spaces asynchronously. Destroying
    or hiding Qt's children during that animation can leave the native frame on
    screen as a blank white window. Keep the complete dialog alive until the
    exit is quiet, restore its frozen normal frame, explicitly order out the
    native window, and only then replay close().
    """
    if bool(getattr(widget, "_folder_manager_force_close_replay", False)):
        setattr(widget, "_folder_manager_force_close_replay", False)
        return False
    if sys.platform != "darwin":
        return False
    try:
        state = widget.windowState()
    except (AttributeError, RuntimeError):
        return False
    expanded = bool(state & (Qt.WindowFullScreen | Qt.WindowMaximized))
    pending = bool(getattr(widget, "_folder_manager_close_after_expanded_exit", False))
    if pending:
        event.ignore()
        return True
    if not expanded:
        return False

    event.ignore()
    capture_standard_window_geometry(widget, key)
    generation = int(getattr(widget, "_folder_manager_close_generation", 0)) + 1
    started_at = time.monotonic()
    setattr(widget, "_folder_manager_close_generation", generation)
    setattr(widget, "_folder_manager_close_after_expanded_exit", True)
    setattr(widget, "_folder_manager_close_exit_started_at", started_at)
    setattr(widget, "_folder_manager_close_exit_fallback", False)
    setattr(widget, "_folder_manager_restore_last_state_change", started_at)
    debug_log(
        "window",
        "deferring close until native fullscreen exit finishes",
        force=True,
        widget=widget.__class__.__name__,
        fullscreen=bool(state & Qt.WindowFullScreen),
        maximized=bool(state & Qt.WindowMaximized),
    )

    # Hide the native frame *before* starting the asynchronous Space exit.
    # The dialog remains alive, but the user never sees Cocoa's temporary empty
    # content view while Qt waits for the fullscreen transition to settle.
    native = macos_native_window(widget)
    if native is not None:
        try:
            native.orderOut_(None)
            setattr(widget, "_folder_manager_close_native_hidden", True)
        except Exception:
            pass

    if state & Qt.WindowFullScreen:
        if not toggle_macos_native_fullscreen(widget):
            setattr(widget, "_folder_manager_close_exit_fallback", True)
            widget.showNormal()
    else:
        setattr(widget, "_folder_manager_close_exit_fallback", True)
        widget.showNormal()

    QTimer.singleShot(
        180,
        lambda: finish_deferred_window_close(widget, key, generation),
    )
    return True


def finish_deferred_window_close(widget: QWidget, key: str, generation: int):
    if generation != int(getattr(widget, "_folder_manager_close_generation", 0)):
        return
    if not bool(getattr(widget, "_folder_manager_close_after_expanded_exit", False)):
        return
    try:
        now = time.monotonic()
        state = widget.windowState()
        expanded = bool(state & (Qt.WindowFullScreen | Qt.WindowMaximized))
        if bool(getattr(widget, "_folder_manager_close_native_hidden", False)):
            native = macos_native_window(widget)
            if native is not None:
                try:
                    native.orderOut_(None)
                except Exception:
                    pass
        started_at = float(getattr(widget, "_folder_manager_close_exit_started_at", now))
        if expanded:
            if (
                not bool(getattr(widget, "_folder_manager_close_exit_fallback", False))
                and now - started_at >= 3.0
            ):
                setattr(widget, "_folder_manager_close_exit_fallback", True)
                widget.showNormal()
            if now - started_at < 10.0:
                QTimer.singleShot(
                    180,
                    lambda: finish_deferred_window_close(widget, key, generation),
                )
                return

        last_change = float(
            getattr(widget, "_folder_manager_restore_last_state_change", started_at)
        )
        if not expanded and now - last_change < 0.65:
            QTimer.singleShot(
                180,
                lambda: finish_deferred_window_close(widget, key, generation),
            )
            return

        placement = getattr(widget, "_folder_manager_pre_fullscreen_placement", None)
        target = getattr(widget, "_folder_manager_pre_fullscreen_rect", None)
        if not isinstance(target, QRect) or not target.isValid():
            target = getattr(widget, "_folder_manager_last_windowed_geometry", None)
            placement = getattr(widget, "_folder_manager_last_windowed_placement", placement)
        if not expanded and isinstance(target, QRect) and target.isValid():
            target = restore_rect_for_window_placement(widget, placement, QRect(target))
            widget.setGeometry(target)
            setattr(widget, "_folder_manager_last_windowed_geometry", QRect(target))
            setattr(widget, "_folder_manager_last_windowed_placement", capture_window_placement(widget, target))

        # Invalidate any ordinary restore callback already queued before the
        # close request, then let the replayed closeEvent perform normal cleanup.
        setattr(
            widget,
            "_folder_manager_restore_generation",
            int(getattr(widget, "_folder_manager_restore_generation", 0)) + 1,
        )
        setattr(widget, "_folder_manager_geometry_restore_pending", False)
        setattr(widget, "_folder_manager_fullscreen_cycle", False)
        setattr(widget, "_folder_manager_pre_fullscreen_rect", None)
        setattr(widget, "_folder_manager_pre_fullscreen_placement", None)
        setattr(widget, "_folder_manager_close_after_expanded_exit", False)
        setattr(widget, "_folder_manager_close_native_hidden", False)

        # orderOut removes the actual Cocoa shell before Qt hides its children.
        # It is safe for reusable dialogs; show() orders the same NSWindow back in.
        native = macos_native_window(widget)
        if native is not None:
            native.orderOut_(None)
        setattr(widget, "_folder_manager_force_close_replay", True)
        widget.close()
        debug_log(
            "window",
            "native fullscreen close finished without orphan shell",
            force=True,
            widget=widget.__class__.__name__,
        )
    except RuntimeError:
        return


# ---------------------------------------------------------------------------
# Separate preview window


class LargePreviewDialog(QDialog):
    def __init__(
        self,
        parent,
        step_callback,
        delete_callback,
        meta_provider=None,
        current_path_provider=None,
        embedded_preview_panel=None,
    ):
        # Keep Preview as an independent AppKit window. A native Qt parent makes
        # macOS treat it as part of a transient window family, which can restack
        # or move the whole family when the user switches Spaces. The callers
        # already retain and close this dialog explicitly, so a plain owner
        # reference is enough for lifecycle coordination.
        super().__init__(None)
        self.preview_surface_role = "window"
        self.owner_window = top_level_window_for(parent) or parent
        # Inherit the embedding app's geometry namespace (Delta uses its own
        # QSettings object). This keeps Preview/Debug/Scanner placement behavior
        # identical whether Folder Manager is run directly or embedded.
        try:
            owner_settings = window_geometry_settings(self.owner_window) if self.owner_window is not None else None
            if isinstance(owner_settings, QSettings):
                self._folder_manager_geometry_settings = owner_settings
        except Exception:
            pass
        self.setWindowTitle("Preview")
        self.setWindowFlag(Qt.Window, True)
        self.setWindowModality(Qt.NonModal)
        self.setModal(False)
        self.setFocusPolicy(Qt.StrongFocus)
        self.resize(960, 680)
        try:
            self.setWindowFlag(Qt.WindowType.WindowFullscreenButtonHint, True)
        except Exception:
            try:
                self.setWindowFlag(Qt.WindowFullscreenButtonHint, True)
            except Exception:
                pass
        self.step_callback = step_callback
        self.delete_callback = delete_callback
        self.meta_provider = meta_provider
        self.current_path_provider = current_path_provider
        self.embedded_preview_panel = embedded_preview_panel
        self.current_path: Optional[Path] = None
        self.media_player = None
        self.audio_output = None
        self.media_devices = None
        self.audio_monitor = None
        self.video_widget = None
        self.scrubbing_video = False
        self.scrub_was_playing = False
        self.media_duration_ms = 0
        self.metadata_duration_ms = 0
        self.pending_media_seek_ms: Optional[int] = None
        self.current_media_meta = MediaMeta()
        self.media_controls_available = False
        self.media_dimmed = False
        # This is the large window's logical state. QMediaPlayer may advertise
        # PausedState while loading or seeking; that must not change the badge,
        # autoplay on row navigation, or the user's intent.
        self.playback_paused_by_user = False
        self.temporary_playback_override = False
        self.global_playback_lock_owners: List[object] = []
        self.priming_paused_frame = False
        self.thumbnail_request_id = 0
        self.thumbnail_workers: List[PreviewThumbnailWorker] = []
        self.playable_proxy_workers: List[PreviewPlayableProxyWorker] = []
        self.playable_proxy_request_id = 0
        self.playable_proxy_source: Optional[Path] = None
        self.playing_compatibility_proxy = False
        # Exact proxy pathname currently bound to QMediaPlayer.  The paired
        # embedded surface can publish a dot-prefixed growing stream while this
        # window's own worker waits for the final cache. Tracking the pathname
        # makes that two-signal race idempotent and keeps late buffer events
        # from rebinding an obsolete temporary.
        self.bound_compatibility_proxy_path: Optional[Path] = None
        # A growing MPEG-TS can be rejected by Qt before the worker atomically
        # publishes the completed cache. Keep that future handoff explicit so
        # finalization can recover instead of leaving a permanent poster.
        self.awaiting_final_proxy = False
        self._proxy_rebind_pending = False
        self._proxy_rebind_generation = 0
        self._provisional_resume_position_ms = 0
        self.playback_recovery_source: Optional[Path] = None
        self._debug_last_media_status = None
        self._debug_last_playback_state = None
        self._debug_last_capability_signature = None
        self._debug_last_error_signature = None
        self._debug_first_frame_key = None
        self._debug_source_started_at = 0.0
        self._debug_media_descriptor: Dict[str, object] = {}
        self.text_workers: List[PreviewTextWorker] = []
        self.video_poster_timer = QTimer(self)
        self.video_poster_timer.setSingleShot(True)
        self.video_poster_timer.timeout.connect(self.start_pending_video_artwork)
        self.pending_video_poster_path: Optional[Path] = None
        # Row navigation has a different cadence from an explicit open. Keep the
        # currently painted frame still and silent while arrow/wheel bursts settle,
        # then load only the final row. This avoids one QMediaPlayer teardown and
        # one ffmpeg proxy worker for every intermediate selection.
        self.queued_path_timer = QTimer(self)
        self.queued_path_timer.setSingleShot(True)
        self.queued_path_timer.timeout.connect(self.apply_queued_path)
        self.queued_preview_path: Optional[Path] = None
        self.queued_preview_meta: Optional[MediaMeta] = None
        self.queued_transport_quiesced = False
        self.queued_transport_should_resume = False
        self.queued_path_started_at = 0.0
        self.queued_path_change_count = 0
        self.scrub_seeker = PreviewSeekController(lambda: self.media_player, self)
        self.seek_hold_direction = 0
        self.seek_hold_active = False
        self.seek_hold_last_at = 0.0
        self.seek_hold_restore_pause = False
        self.suppress_next_end_countdown = False
        self.seek_boundary_margin_ms = 850
        self.cinema_chrome_hidden = False
        self.chrome_fade_generation = 0
        self.chrome_overlay_mode = False
        self.exiting_cinema = False
        self.windowed_geometry_before_cinema: Optional[QRect] = None
        self.windowed_placement_before_cinema: Optional[Dict[str, object]] = None
        # Keep the exit target independently from the active cinema session.
        # macOS can deliver delayed fullscreen geometry after its state flags
        # have cleared, so ownership remains here until several stable checks.
        self.cinema_restore_geometry: Optional[QRect] = None
        self.cinema_session_id = 0
        self.last_windowed_geometry: Optional[QRect] = None
        self.opening_windowed_geometry: Optional[QRect] = None
        self.last_windowed_placement: Optional[Dict[str, object]] = None
        self.opening_windowed_placement: Optional[Dict[str, object]] = None
        self.last_debug_windowed_geometry: Optional[QRect] = None
        self.cinema_overlay_window = None
        self.settings = app_settings()
        self.preview_muted = settings_bool(
            self.settings,
            "preview/muted",
            settings_bool(self.settings, "large_preview/muted", True),
        )
        self.seek_hold_delay = QTimer(self)
        self.seek_hold_delay.setSingleShot(True)
        self.seek_hold_delay.timeout.connect(self.start_continuous_seek)
        self.seek_hold_timer = QTimer(self)
        self.seek_hold_timer.setInterval(30)
        self.seek_hold_timer.timeout.connect(self.continuous_seek_tick)
        self.windowed_geometry_settle_timer = QTimer(self)
        self.windowed_geometry_settle_timer.setSingleShot(True)
        self.windowed_geometry_settle_timer.setInterval(300)
        self.windowed_geometry_settle_timer.timeout.connect(self.remember_current_windowed_geometry)
        self.cinema_restore_verify_timer = QTimer(self)
        self.cinema_restore_verify_timer.setSingleShot(True)
        self.cinema_restore_verify_timer.setInterval(140)
        self.cinema_restore_verify_timer.timeout.connect(self.verify_cinema_restore_geometry)
        self.cinema_restore_verify_attempts = 0
        self.cinema_restore_stable_checks = 0
        self.cinema_restore_verify_deadline = 0.0
        self.cinema_restore_started_at = 0.0
        self.cinema_restore_last_state_change = 0.0
        self.cinema_restore_fallback_issued = False
        self.cinema_restore_geometry_applied = False
        self.cinema_restore_context_prepared = False
        self.cinema_entry_pending = False
        self.video_click_timer = QTimer(self)
        self.video_click_timer.setSingleShot(True)
        self.video_click_timer.timeout.connect(self.toggle_cinema_chrome_by_click)
        self.cinema_timer = QTimer(self)
        self.cinema_timer.setSingleShot(True)
        self.cinema_timer.timeout.connect(self.hide_cinema_chrome_if_idle)
        self.auto_next_timer = QTimer(self)
        self.auto_next_timer.setInterval(1000)
        self.auto_next_timer.timeout.connect(self.tick_auto_next_countdown)
        self.auto_next_seconds = 0
        self.auto_next_source_path: Optional[Path] = None
        self.setMouseTracking(True)
        self.escape_shortcut = QShortcut(QKeySequence(Qt.Key_Escape), self)
        self.escape_shortcut.setContext(Qt.WindowShortcut)
        self.escape_shortcut.activated.connect(self.handle_escape_shortcut)
        self.space_shortcut = QShortcut(QKeySequence(Qt.Key_Space), self)
        # Keep Space local to the preview window. ApplicationShortcut can steal
        # Space from the main file table, preventing Space from opening preview.
        # WindowShortcut still works in cinema/fullscreen because the video widget
        # and controls are children of this dialog.
        self.space_shortcut.setContext(Qt.WindowShortcut)
        self.space_shortcut.activated.connect(self.handle_space_shortcut)

        self.preview_layout = QVBoxLayout(self)
        self.preview_layout.setContentsMargins(14, 14, 14, 14)
        self.preview_layout.setSpacing(10)

        self.header_widget = QWidget()
        self.header_widget.setObjectName("PreviewChrome")
        self.header_widget.setMouseTracking(True)
        self.header_widget.installEventFilter(self)
        self.header_layout = QHBoxLayout()
        self.header_widget.setLayout(self.header_layout)
        self.header_layout.setContentsMargins(0, 0, 0, 0)
        self.header_layout.setSpacing(8)
        self.preview_layout.addWidget(self.header_widget)
        self.title_label = QLabel("Preview")
        self.title_label.setObjectName("SectionTitle")
        self.meta_label = QLabel("")
        self.meta_label.setObjectName("MutedLabel")
        title_box = QVBoxLayout()
        title_box.setSpacing(1)
        title_box.addWidget(self.title_label)
        title_box.addWidget(self.meta_label)
        self.header_layout.addLayout(title_box, stretch=1)
        self.fullscreen_btn = QPushButton("Full Screen", self.header_widget)
        self.fullscreen_btn.clicked.connect(self.toggle_full_screen)
        self.fullscreen_btn.hide()
        self.close_btn = QPushButton("Close", self.header_widget)
        self.close_btn.clicked.connect(self.close)
        self.close_btn.hide()

        self.stack = QStackedWidget()
        self.stack.setObjectName("LargePreviewStack")
        self.stack.setMouseTracking(True)
        self.stack.installEventFilter(self)
        self.preview_layout.addWidget(self.stack, stretch=1)
        self.cinema_click_catcher = QWidget(self.stack)
        self.cinema_click_catcher.setObjectName("CinemaClickCatcher")
        self.cinema_click_catcher.setMouseTracking(True)
        self.cinema_click_catcher.setStyleSheet("background: transparent;")
        self.cinema_click_catcher.installEventFilter(self)
        self.cinema_click_catcher.hide()
        self.auto_next_label = QLabel(self.stack)
        self.auto_next_label.setObjectName("CinemaCountdown")
        self.auto_next_label.setAlignment(Qt.AlignRight | Qt.AlignVCenter)
        self.auto_next_label.setAttribute(Qt.WA_TransparentForMouseEvents, True)
        self.auto_next_label.hide()

        self.placeholder = QLabel("No preview")
        self.placeholder.setAlignment(Qt.AlignCenter)
        self.placeholder.setWordWrap(True)
        self.placeholder.setContentsMargins(16, 10, 16, 10)
        self.placeholder.setObjectName("LargePreviewPlaceholder")
        self.placeholder.setMouseTracking(True)
        self.placeholder.installEventFilter(self)
        self.stack.addWidget(self.placeholder)

        self.image_label = AspectPixmapLabel()
        self.image_label.setAlignment(Qt.AlignCenter)
        self.image_label.setObjectName("LargeImagePreview")
        self.image_label.setMouseTracking(True)
        self.image_label.installEventFilter(self)
        self.stack.addWidget(self.image_label)

        self.text_view = QTextEdit()
        self.text_view.setReadOnly(True)
        self.text_view.setObjectName("LargeTextPreview")
        self.text_view.setFocusPolicy(Qt.NoFocus)
        self.text_view.setMouseTracking(True)
        self.text_view.viewport().setMouseTracking(True)
        self.text_view.installEventFilter(self)
        self.text_view.viewport().installEventFilter(self)
        self.stack.addWidget(self.text_view)

        if MEDIA_PREVIEW_AVAILABLE and QMediaPlayer and QAudioOutput and QVideoSink:
            # Coalesce decoder bursts to the active display's cadence so high
            # frame-rate media stays smooth without converting invisible frames.
            # Keep the decoded source resolution: a video paused in a normal
            # window remains sharp after entering fullscreen or resizing.
            self.video_widget = FrameVideoWidget(retain_source_resolution=True)
            self.video_widget.setObjectName("LargeVideoPreview")
            self.video_widget.setMouseTracking(True)
            self.video_widget.installEventFilter(self)
            self.stack.addWidget(self.video_widget)
            self.paused_overlay = QLabel("-paused-", self.stack)
            self.paused_overlay.setObjectName("PausedOverlay")
            self.paused_overlay.setAlignment(Qt.AlignCenter)
            self.paused_overlay.setAttribute(Qt.WA_TransparentForMouseEvents, True)
            self.paused_overlay.setAttribute(Qt.WA_StyledBackground, True)
            self.paused_overlay.setStyleSheet(PAUSED_OVERLAY_STYLE)
            self.paused_overlay.hide()
            self.audio_output = QAudioOutput(self)
            self.media_devices = follow_system_audio_output(self, self.audio_output)
            self.media_player = QMediaPlayer(self)
            self.media_player.setAudioOutput(self.audio_output)
            self.media_player.setVideoSink(self.video_widget.video_sink)
            self.audio_monitor = install_preview_audio_diagnostics(
                self,
                self.media_player,
                self.audio_output,
                "window",
            )
            self.video_widget.firstFrameReady.connect(self.on_video_first_frame_ready)
            self.video_widget.frameConversionUnavailable.connect(self.on_video_frame_conversion_unavailable)
            self.media_player.durationChanged.connect(self.on_duration_changed)
            self.media_player.positionChanged.connect(self.on_position_changed)
            self.media_player.playbackStateChanged.connect(self.on_playback_state_changed)
            self.media_player.mediaStatusChanged.connect(self.on_media_status_changed)
            self.media_player.errorOccurred.connect(self.on_video_playback_error)
            for signal_name in (
                "hasVideoChanged",
                "hasAudioChanged",
                "tracksChanged",
                "seekableChanged",
                "bufferProgressChanged",
                "sourceChanged",
            ):
                signal = getattr(self.media_player, signal_name, None)
                if signal is not None:
                    signal.connect(lambda *_args: self.on_video_capabilities_changed())

        self.controls_widget = QWidget()
        self.controls_widget.setObjectName("PreviewChrome")
        self.controls_widget.setMouseTracking(True)
        self.controls_widget.installEventFilter(self)
        self.controls_layout = QHBoxLayout()
        self.controls_widget.setLayout(self.controls_layout)
        self.controls_layout.setContentsMargins(0, 0, 0, 0)
        self.controls_layout.setSpacing(8)
        self.preview_layout.addWidget(self.controls_widget)
        self.play_button = QPushButton("▶")
        self.play_button.setObjectName("PreviewPlayButton")
        self.play_button.setFixedWidth(44)
        self.play_button.setToolTip("Play / pause")
        self.play_button.setFocusPolicy(Qt.NoFocus)
        self.play_button.clicked.connect(self.toggle_video_playback)
        self.controls_layout.addWidget(self.play_button)
        self.scrub_slider = QSlider(Qt.Horizontal)
        self.scrub_slider.setObjectName("PreviewScrubSlider")
        self.scrub_slider.setFocusPolicy(Qt.NoFocus)
        self.scrub_slider.setRange(0, 0)
        self.scrub_slider.sliderPressed.connect(self.on_scrub_pressed)
        self.scrub_slider.sliderReleased.connect(self.on_scrub_released)
        self.scrub_slider.sliderMoved.connect(self.on_scrub_moved)
        self.scrub_slider.installEventFilter(self)
        self.controls_layout.addWidget(self.scrub_slider, stretch=1)
        self.time_label = QLabel("0:00 / 0:00")
        self.time_label.setObjectName("MutedLabel")
        self.time_label.setFixedWidth(110)
        self.controls_layout.addWidget(self.time_label)
        self.mute_button = QPushButton("Muted")
        self.mute_button.setFocusPolicy(Qt.NoFocus)
        self.mute_button.setFixedWidth(86)
        self.mute_button.clicked.connect(self.toggle_mute)
        self.controls_layout.addWidget(self.mute_button)
        self.apply_mute()

        self.header_opacity = QGraphicsOpacityEffect(self.header_widget)
        self.header_opacity.setOpacity(1.0)
        self.header_widget.setGraphicsEffect(self.header_opacity)
        self.controls_opacity = QGraphicsOpacityEffect(self.controls_widget)
        self.controls_opacity.setOpacity(1.0)
        self.controls_widget.setGraphicsEffect(self.controls_opacity)
        self.header_fade = QPropertyAnimation(self.header_opacity, b"opacity", self)
        self.controls_fade = QPropertyAnimation(self.controls_opacity, b"opacity", self)
        for animation in (self.header_fade, self.controls_fade):
            animation.setDuration(220)
            animation.setEasingCurve(QEasingCurve.OutCubic)

        for hover_widget in (
            self,
            self.stack,
            self.placeholder,
            self.image_label,
            self.text_view,
            self.text_view.viewport(),
            self.video_widget,
            self.header_widget,
            self.controls_widget,
        ):
            if hover_widget is None:
                continue
            hover_widget.setMouseTracking(True)
            hover_widget.setAttribute(Qt.WA_Hover, True)

        self.build_cinema_overlay_window()

        register_video_owner(self)
        self.destroyed.connect(lambda *_args: unregister_video_owner(self))
        app = QApplication.instance()
        if app is not None:
            app.aboutToQuit.connect(self.stop_preview_workers)
            app.installEventFilter(self)
            try:
                app.applicationStateChanged.connect(self.on_application_state_changed)
            except Exception:
                pass
        metadata_loaded = getattr(self.embedded_preview_panel, "metadataLoaded", None)
        if metadata_loaded is not None:
            try:
                metadata_loaded.connect(self.on_external_metadata_loaded)
            except (AttributeError, RuntimeError, TypeError):
                pass
        # Use the same settled normal-window geometry discipline as Debug and
        # both scanners. The cinema-specific logic still owns fullscreen, while
        # this supplies a stable normal rectangle + monitor identity across opens.
        configure_settled_window_geometry(self, "preview", QSize(960, 680))
        stable = getattr(self, "_folder_manager_last_windowed_geometry", None)
        if isinstance(stable, QRect) and stable.isValid():
            self.last_windowed_geometry = QRect(stable)
            self.opening_windowed_geometry = QRect(stable)
            placement = getattr(self, "_folder_manager_last_windowed_placement", None)
            self.last_windowed_placement = placement or capture_window_placement(self, stable)
            self.opening_windowed_placement = self.last_windowed_placement

    def build_cinema_overlay_window(self):
        # This is an ordinary child overlay. The video is painted by Qt too, so no
        # native layer or cross-Space workaround is needed.
        self.cinema_overlay_window = QWidget(self)
        self.cinema_overlay_window.setObjectName("CinemaChromeLayer")
        self.cinema_overlay_window.setAttribute(Qt.WA_StyledBackground, True)
        self.cinema_overlay_window.setStyleSheet("background: transparent; border: none;")
        self.cinema_overlay_window.setFocusPolicy(Qt.NoFocus)
        self.cinema_overlay_window.setMouseTracking(True)
        self.cinema_overlay_window.installEventFilter(self)
        self.cinema_overlay_window.hide()

    def hide_cinema_overlay_window(self, hide_pause_badge: bool = False):
        if self.cinema_overlay_window is not None:
            self.cinema_overlay_window.hide()
        if hide_pause_badge and hasattr(self, "paused_overlay"):
            self.paused_overlay.hide()

    def update_cinema_overlay_mask(self):
        overlay = self.cinema_overlay_window
        if overlay is None or not self.chrome_overlay_mode:
            return
        region = QRegion()
        if self.header_widget.isVisible():
            region = region.united(QRegion(self.header_widget.geometry()))
        if self.media_controls_available and self.controls_widget.isVisible():
            region = region.united(QRegion(self.controls_widget.geometry()))
        overlay.setMask(region)

    def sync_cinema_overlay_window(self, raise_window: bool = False) -> bool:
        overlay = self.cinema_overlay_window
        if overlay is None or not self.chrome_overlay_mode:
            return False
        overlay.setGeometry(self.rect())
        overlay.show()
        if raise_window:
            overlay.raise_()
        self.update_cinema_overlay_mask()
        return True

    def stop_preview_workers(self):
        self.cancel_queued_path(resume_current=False)
        self.cancel_video_artwork_fallback(cancel_worker=True)
        self.playable_proxy_request_id += 1
        self.playable_proxy_source = None
        self.playing_compatibility_proxy = False
        self.bound_compatibility_proxy_path = None
        self.awaiting_final_proxy = False
        self.playback_recovery_source = None
        workers = list(self.thumbnail_workers) + list(self.text_workers) + list(self.playable_proxy_workers)
        stop_preview_worker_collection(workers, wait_for_exit=False)
        self.thumbnail_workers.clear()
        self.text_workers.clear()
        self.playable_proxy_workers.clear()

    def interrupt_stale_preview_workers(self, path: Path):
        for worker in list(self.thumbnail_workers) + list(self.text_workers) + list(self.playable_proxy_workers):
            if getattr(worker, "path", None) == path:
                continue
            try:
                if worker.isRunning():
                    worker.cancel()
            except RuntimeError:
                pass

    def eventFilter(self, watched, event):
        owner_window = top_level_window_for(self.owner_window)
        if (
            event.type() == QEvent.WindowActivate
            and owner_window is not None
            and watched is owner_window
        ):
            # The normal Preview is app-relative frontmost, not globally
            # always-on-top.  Raise without activating so a click in the main
            # window keeps its focus and does not start an activation loop.
            QTimer.singleShot(
                0,
                lambda: self.keep_windowed_preview_above_owner("owner activated"),
            )
        if watched is getattr(self, "scrub_slider", None):
            if handle_preview_seek_mouse(self, self.scrub_slider, event):
                slider_kinds = {
                    QEvent.MouseButtonPress: "slider-press",
                    QEvent.MouseMove: "slider-drag",
                    QEvent.MouseButtonRelease: "slider-release",
                }
                kind = slider_kinds.get(event.type())
                if kind:
                    record_consumed_preview_interaction(self.scrub_slider, event, kind)
                # Clicking/dragging the timeline must not permanently hand
                # keyboard ownership to the slider. Return focus to Quick Look.
                QTimer.singleShot(0, self.ensure_preview_input_focus)
                return True
        key_event_types = (QEvent.KeyPress, QEvent.KeyRelease, QEvent.ShortcutOverride)
        key = event.key() if event.type() in key_event_types else None
        preview_keys = {
            Qt.Key_Escape,
            Qt.Key_Space,
            Qt.Key_Return,
            Qt.Key_Enter,
            Qt.Key_Left,
            Qt.Key_Right,
            Qt.Key_Up,
            Qt.Key_Down,
            Qt.Key_Delete,
            Qt.Key_Backspace,
            Qt.Key_F,
        }
        if key in preview_keys and self.preview_owns_input_event(watched):
            if event.type() == QEvent.ShortcutOverride:
                # Prevent focused buttons/sliders/text widgets and macOS native
                # shortcuts from consuming Quick Look's navigation keys.
                event.accept()
                return True
            if event.type() == QEvent.KeyPress:
                record_consumed_preview_interaction(
                    _interaction_semantic_widget(watched),
                    event,
                    "key-press",
                    key=_interaction_key_name(event) or qt_enum_name(key),
                    auto_repeat=bool(event.isAutoRepeat()),
                )
                self.keyPressEvent(event)
            elif key in (Qt.Key_Left, Qt.Key_Right):
                record_consumed_preview_interaction(
                    _interaction_semantic_widget(watched),
                    event,
                    "key-release",
                    key=_interaction_key_name(event) or qt_enum_name(key),
                    auto_repeat=bool(event.isAutoRepeat()),
                )
                self.keyReleaseEvent(event)
            if event.isAccepted():
                return True
        if (
            event.type() == QEvent.KeyPress
            and self.isVisible()
            and self.isActiveWindow()
            and (self.isFullScreen() or self.chrome_overlay_mode or bool(self.property("cinema")))
        ):
            if event.key() == Qt.Key_Escape:
                if event.isAutoRepeat():
                    event.accept()
                    return True
                self.handle_escape_shortcut()
                event.accept()
                return True
            if event.key() == Qt.Key_Space:
                if event.isAutoRepeat():
                    event.accept()
                    return True
                self.handle_space_shortcut()
                event.accept()
                return True
        if event.type() in (QEvent.MouseMove, QEvent.HoverMove, QEvent.Enter):
            self.handle_cinema_mouse_activity()
        if watched is getattr(self, "cinema_overlay_window", None) and event.type() == QEvent.KeyPress:
            if event.key() == Qt.Key_Escape:
                self.handle_escape_shortcut()
                event.accept()
                return True
            if event.key() == Qt.Key_Space:
                self.handle_space_shortcut()
                event.accept()
                return True
        media_surface_widgets = (
            getattr(self, "video_widget", None),
            getattr(self, "image_label", None),
            getattr(self, "placeholder", None),
            getattr(self, "stack", None),
        )
        media_surface = watched in media_surface_widgets
        if media_surface and event.type() == QEvent.MouseButtonDblClick and event.button() == Qt.LeftButton:
            record_consumed_preview_interaction(watched, event, "mouse-double-click")
            self.video_click_timer.stop()
            self.toggle_video_playback()
            event.accept()
            return True
        if media_surface and event.type() == QEvent.MouseButtonPress and event.button() == Qt.LeftButton:
            record_consumed_preview_interaction(watched, event, "mouse-click")
            if self.isFullScreen():
                self.video_click_timer.stop()
                self.toggle_cinema_chrome_by_click()
            else:
                self.toggle_video_playback()
            event.accept()
            return True
        return super().eventFilter(watched, event)

    def preview_owns_input_event(self, watched) -> bool:
        """Accept keys from any child without letting controls steal shortcuts."""
        if not self.isVisible():
            return False
        try:
            if self.isActiveWindow() or QApplication.activeWindow() is self:
                return True
        except RuntimeError:
            return False
        current = watched if isinstance(watched, QObject) else None
        seen: set[int] = set()
        while current is not None and id(current) not in seen:
            if current is self:
                return True
            seen.add(id(current))
            try:
                current = current.parent()
            except (AttributeError, RuntimeError):
                break
        return False

    def mouseMoveEvent(self, event):
        self.handle_cinema_mouse_activity()
        super().mouseMoveEvent(event)

    def on_application_state_changed(self, state):
        if not application_is_active():
            self.cinema_timer.stop()
            return
        if self.isVisible() and not self.isFullScreen() and not self.chrome_overlay_mode:
            QTimer.singleShot(
                0,
                lambda: self.keep_windowed_preview_above_owner("application activated"),
            )
        if self.isVisible() and self.isFullScreen() and self.isActiveWindow():
            QTimer.singleShot(0, self.restore_cinema_after_activation)

    def keep_windowed_preview_above_owner(self, reason: str = "owner ordering") -> bool:
        """Keep a normal Preview above its app without globally floating it."""
        if (
            not application_is_active()
            or not self.isVisible()
            or self.isFullScreen()
            or self.chrome_overlay_mode
            or self.exiting_cinema
        ):
            return False
        owner_window = top_level_window_for(self.owner_window)
        if owner_window is None or owner_window is self:
            return False
        active_window = QApplication.activeWindow()
        if active_window is not None and active_window not in (owner_window, self):
            return False
        try:
            self.raise_()
        except (AttributeError, RuntimeError):
            return False
        debug_log(
            "window",
            "windowed preview restacked above owner",
            reason=reason,
            active_window=(active_window.__class__.__name__ if active_window else "none"),
        )
        return True

    def restore_cinema_after_activation(self):
        if not self.isVisible() or not self.isFullScreen() or not self.isActiveWindow() or self.exiting_cinema:
            return
        self.show_cinema_chrome(schedule_hide=self.media_is_playing())
        if getattr(self, "media_dimmed", False):
            self.set_dimmed(True)

    def media_is_playing(self) -> bool:
        if self.media_player is None or QMediaPlayer is None:
            return False
        try:
            return self.media_player.playbackState() == QMediaPlayer.PlaybackState.PlayingState
        except Exception:
            return False

    def cursor_on_cinema_chrome(self) -> bool:
        if self.cinema_chrome_hidden:
            return False
        cursor_pos = QCursor.pos()
        for widget in (self.header_widget, self.controls_widget):
            if widget.isVisible() and widget.rect().contains(widget.mapFromGlobal(cursor_pos)):
                return True
        return False

    def handle_cinema_mouse_activity(self):
        # The dialog installs an application-wide event filter, so mouse moves
        # from the main window arrive here too. Never raise or alter cinema chrome
        # unless this fullscreen preview is the active window on the current Space.
        if (
            not self.isFullScreen()
            or not self.isVisible()
            or not self.isActiveWindow()
            or not application_is_active()
        ):
            return
        local = self.mapFromGlobal(QCursor.pos())
        if not self.rect().contains(local):
            return
        if self.cinema_chrome_hidden:
            self.show_cinema_chrome(schedule_hide=True)
            return
        self.schedule_cinema_hide()

    def schedule_cinema_hide(self):
        if not self.isFullScreen() or not self.isVisible() or not self.media_is_playing():
            self.cinema_timer.stop()
            return
        if self.cursor_on_cinema_chrome():
            self.cinema_timer.stop()
            return
        self.cinema_timer.start(3000)

    def hide_cinema_chrome_if_idle(self):
        if not self.isFullScreen() or not self.media_is_playing() or self.cursor_on_cinema_chrome():
            return
        self.fade_cinema_chrome_to(0.0, hide_after=True)

    def show_cinema_chrome(self, schedule_hide: bool = False):
        if self.exiting_cinema:
            return
        self.position_cinema_chrome()
        self.header_widget.show()
        if self.media_controls_available:
            self.controls_widget.show()
        else:
            self.controls_widget.hide()
        self.cinema_chrome_hidden = False
        # Native child layers on macOS do not reliably repaint while a
        # QGraphicsOpacityEffect is fading in. Wake chrome synchronously so mouse
        # movement always produces visible controls; fade-out remains animated.
        self.header_fade.stop()
        self.controls_fade.stop()
        self.header_opacity.setOpacity(1.0)
        self.controls_opacity.setOpacity(1.0)
        if getattr(self, "media_dimmed", False):
            self.set_dimmed(True)
        elif hasattr(self, "paused_overlay") and self.paused_overlay.isVisible():
            self.paused_overlay.raise_()
        if hasattr(self, "auto_next_label") and self.auto_next_label.isVisible():
            self.auto_next_label.raise_()
        self.header_widget.raise_()
        self.controls_widget.raise_()
        self.sync_cinema_overlay_window(raise_window=True)
        self.update_cinema_overlay_mask()
        if hasattr(self, "paused_overlay") and self.paused_overlay.isVisible():
            self.paused_overlay.raise_()
        if schedule_hide:
            self.schedule_cinema_hide()

    def toggle_cinema_chrome_by_click(self):
        if not self.isFullScreen():
            return
        if self.cinema_chrome_hidden:
            self.show_cinema_chrome(schedule_hide=self.media_is_playing())
        else:
            if self.cursor_on_cinema_chrome():
                return
            self.cinema_timer.stop()
            self.fade_cinema_chrome_to(0.0, hide_after=True)

    def fade_cinema_chrome_to(self, opacity: float, hide_after: bool = False):
        if not hasattr(self, "header_fade"):
            return
        if not self.isFullScreen() and hide_after:
            return
        self.chrome_fade_generation += 1
        generation = self.chrome_fade_generation
        self.sync_cinema_overlay_window(raise_window=True)
        self.header_widget.show()
        if self.media_controls_available:
            self.controls_widget.show()
            pairs = (
                (self.header_fade, self.header_opacity),
                (self.controls_fade, self.controls_opacity),
            )
        else:
            self.controls_widget.hide()
            pairs = ((self.header_fade, self.header_opacity),)
        for animation, effect in pairs:
            animation.stop()
            animation.setStartValue(effect.opacity())
            animation.setEndValue(opacity)
            animation.start()
        self.update_cinema_overlay_mask()
        if hide_after:
            self.cinema_chrome_hidden = True
            QTimer.singleShot(230, lambda: self.finish_chrome_hide(generation))
        else:
            self.cinema_chrome_hidden = False

    def finish_chrome_hide(self, generation: int):
        if not self.isFullScreen() or generation != self.chrome_fade_generation or not self.cinema_chrome_hidden:
            return
        self.header_widget.hide()
        self.controls_widget.hide()
        self.hide_cinema_overlay_window(hide_pause_badge=False)

    def enter_cinema_overlay_mode(self):
        # Keep all cinema UI as children of this dialog. This keeps the title,
        # controls, and pause badge tied to the same window/Space as the video.
        if self.chrome_overlay_mode:
            self.position_cinema_chrome()
            return
        self.chrome_overlay_mode = True
        self.preview_layout.removeWidget(self.header_widget)
        self.preview_layout.removeWidget(self.controls_widget)
        self.header_widget.setParent(self.cinema_overlay_window)
        self.controls_widget.setParent(self.cinema_overlay_window)
        self.cinema_click_catcher.hide()
        self.header_widget.show()
        if self.media_controls_available:
            self.controls_widget.show()
        self.position_cinema_chrome()

    def leave_cinema_overlay_mode(self):
        was_overlay = self.chrome_overlay_mode
        self.hide_cinema_overlay_window()
        self.cinema_timer.stop()
        self.header_fade.stop()
        self.controls_fade.stop()
        self.header_opacity.setOpacity(1.0)
        self.controls_opacity.setOpacity(1.0)
        self.cinema_chrome_hidden = False
        self.chrome_overlay_mode = False
        if was_overlay:
            self.preview_layout.insertWidget(0, self.header_widget)
            self.preview_layout.addWidget(self.controls_widget)
        self.header_widget.show()
        if self.media_controls_available:
            self.controls_widget.show()
        else:
            self.controls_widget.hide()
        self.cinema_click_catcher.hide()

    def position_cinema_chrome(self):
        if not self.chrome_overlay_mode:
            self.hide_cinema_overlay_window()
            return
        margin = 24
        top_margin = 58 if self.isFullScreen() else margin
        overlay = self.cinema_overlay_window
        if overlay is not None:
            overlay.setGeometry(self.rect())
        chrome_width = max(1, self.width() - 2 * margin)
        header_height = max(58, self.header_widget.sizeHint().height())
        controls_height = max(52, self.controls_widget.sizeHint().height())
        self.header_widget.setGeometry(margin, top_margin, chrome_width, header_height)
        self.controls_widget.setGeometry(
            margin,
            max(margin, self.height() - controls_height - margin),
            chrome_width,
            controls_height,
        )
        self.position_cinema_overlays()
        if hasattr(self, "paused_overlay") and self.paused_overlay.isVisible():
            self.paused_overlay.raise_()
        if self.auto_next_label.isVisible():
            self.auto_next_label.raise_()
        self.header_widget.raise_()
        self.controls_widget.raise_()
        self.update_cinema_overlay_mask()

    def position_cinema_overlays(self):
        if not hasattr(self, "auto_next_label"):
            return
        overlay_size = self.stack.size()
        margin = 32 if self.isFullScreen() else 18

        countdown_size = QSize(250, 58)
        self.auto_next_label.setFixedSize(countdown_size)
        self.auto_next_label.move(
            max(margin, overlay_size.width() - countdown_size.width() - margin),
            max(margin, overlay_size.height() - countdown_size.height() - margin),
        )
        if hasattr(self, "paused_overlay"):
            self.paused_overlay.setGeometry(self.stack.rect())
        if self.chrome_overlay_mode:
            self.update_cinema_overlay_mask()

    def cancel_auto_next_countdown(self):
        self.auto_next_timer.stop()
        self.auto_next_seconds = 0
        self.auto_next_source_path = None
        if hasattr(self, "auto_next_label"):
            self.auto_next_label.hide()

    def start_auto_next_countdown(self):
        if (
            not self.isFullScreen()
            or not self.current_path
            or not is_video_path(self.current_path)
        ):
            return
        self.auto_next_source_path = self.current_path
        self.auto_next_seconds = 3
        self.position_cinema_overlays()
        self.auto_next_label.setText(f"Next video in {self.auto_next_seconds}")
        self.auto_next_label.show()
        self.auto_next_label.raise_()
        self.auto_next_timer.start()

    def tick_auto_next_countdown(self):
        self.auto_next_seconds -= 1
        if self.auto_next_seconds > 0:
            self.auto_next_label.setText(f"Next video in {self.auto_next_seconds}")
            self.auto_next_label.show()
            self.auto_next_label.raise_()
            return

        self.auto_next_timer.stop()
        self.auto_next_label.hide()
        self.advance_to_next_cinema_video()

    def jump_to_next_video_now(self) -> bool:
        if self.auto_next_timer.isActive():
            self.auto_next_timer.stop()
            self.auto_next_label.hide()
            return self.advance_to_next_cinema_video()
        return False

    def advance_to_next_cinema_video(self) -> bool:
        if not self.auto_next_source_path or self.current_path != self.auto_next_source_path:
            return False
        moved = self.step_video_from_boundary(1)
        if not moved:
            self.show_cinema_edge_message("End of list")
        return moved

    def show_cinema_edge_message(self, text: str):
        self.auto_next_timer.stop()
        self.auto_next_seconds = 0
        self.auto_next_label.setText(text)
        self.position_cinema_overlays()
        self.auto_next_label.show()
        self.auto_next_label.raise_()
        QTimer.singleShot(1200, self.auto_next_label.hide)

    def at_media_start(self) -> bool:
        if self.media_player is None:
            return False
        return self.media_player.position() <= self.seek_boundary_margin_ms

    def at_media_end(self) -> bool:
        if self.media_player is None or self.media_duration_ms <= 0:
            return False
        return self.media_player.position() >= max(0, self.media_duration_ms - self.seek_boundary_margin_ms)

    def step_video_from_boundary(self, direction: int) -> bool:
        before = self.current_path
        self.cancel_auto_next_countdown()
        self.suppress_next_end_countdown = False
        try:
            moved = self.step_callback(direction, True)
        except TypeError:
            self.step_callback(direction)
            moved = None
        after = self.current_path_provider() if self.current_path_provider else self.current_path
        if moved is not None:
            return bool(moved)
        return bool(after and after != before)

    def resizeEvent(self, event):
        super().resizeEvent(event)
        self.schedule_windowed_geometry_remember()
        self.position_cinema_overlays()
        self.position_cinema_chrome()

    def moveEvent(self, event):
        super().moveEvent(event)
        self.schedule_windowed_geometry_remember()
        self.position_cinema_chrome()

    def schedule_windowed_geometry_remember(self):
        """Commit a normal-window rectangle only after native resize events settle.

        On macOS the green button resizes a window before Qt reports the maximized
        state. Writing geometry directly from resizeEvent therefore records the
        zoomed rectangle as the supposed Quick Look size. The delayed callback sees
        the final window state and rejects that transition.
        """
        timer = getattr(self, "windowed_geometry_settle_timer", None)
        if timer is None:
            return
        state = self.windowState()
        if (
            self.isFullScreen()
            or bool(state & Qt.WindowMaximized)
            or self.chrome_overlay_mode
            or bool(self.property("cinema"))
            or self.exiting_cinema
            or self.cinema_restore_geometry is not None
        ):
            timer.stop()
            return
        timer.start()

    def geometry_looks_like_macos_zoom(self, geometry: QRect) -> bool:
        return window_geometry_looks_like_macos_zoom(self, geometry)

    def remember_current_windowed_geometry(self):
        """Track only a genuine normal-window rectangle.

        macOS sends a maximized state before the green zoom button is promoted
        to cinema mode. Resize and media-stack events can occur after that, so
        they must not replace the rectangle Escape should restore.
        """
        state = self.windowState()
        if (
            self.isFullScreen()
            or bool(state & Qt.WindowMaximized)
            or self.chrome_overlay_mode
            or bool(self.property("cinema"))
            or self.exiting_cinema
            or self.cinema_restore_geometry is not None
        ):
            return
        geometry = QRect(self.geometry())
        if (
            geometry.isValid()
            and geometry.width() > 0
            and geometry.height() > 0
            and not self.geometry_looks_like_macos_zoom(geometry)
        ):
            previous = self.last_windowed_geometry
            self.last_windowed_geometry = geometry
            self.last_windowed_placement = capture_window_placement(self, geometry)
            if self.last_debug_windowed_geometry != geometry:
                debug_log(
                    "response",
                    "preview window geometry settled",
                    previous_width=previous.width() if previous is not None else 0,
                    previous_height=previous.height() if previous is not None else 0,
                    x=geometry.x(),
                    y=geometry.y(),
                    width=geometry.width(),
                    height=geometry.height(),
                )
                self.last_debug_windowed_geometry = QRect(geometry)

    def capture_windowed_geometry_for_cinema(self):
        """Freeze the normal-window rectangle for one cinema session."""
        if self.windowed_geometry_before_cinema is not None:
            return
        self.windowed_geometry_settle_timer.stop()
        normal_geometry = None
        try:
            normal_geometry = QRect(self.normalGeometry())
        except Exception:
            pass
        # `normalGeometry()` is not stable across a native macOS zoom followed
        # by a media change. `last_windowed_geometry` is recorded only while the
        # dialog is genuinely normal, so it is the authoritative restore target.
        candidates = [
            self.last_windowed_geometry,
            self.opening_windowed_geometry,
            normal_geometry,
        ]
        candidates.append(QRect(self.geometry()))
        sources = ("last-windowed", "opening", "normal", "current")
        for source, candidate in zip(sources, candidates):
            if (
                candidate is not None
                and candidate.isValid()
                and candidate.width() > 0
                and candidate.height() > 0
                and not self.geometry_looks_like_macos_zoom(candidate)
            ):
                self.windowed_geometry_before_cinema = QRect(candidate)
                self.windowed_placement_before_cinema = capture_window_placement(self, candidate)
                debug_log(
                    "large-preview",
                    "captured cinema restore geometry",
                    capture_from=source,
                    x=candidate.x(),
                    y=candidate.y(),
                    width=candidate.width(),
                    height=candidate.height(),
                )
                return

    def event(self, event):
        if event.type() == QEvent.WindowDeactivate:
            # Focus loss is not close intent. Native screenshot dragging, menu
            # interaction, another display, and auxiliary windows can all
            # deactivate Preview. Space, Escape, and the red traffic light are
            # the explicit windowed close actions.
            self.cinema_timer.stop()
        elif event.type() == QEvent.WindowActivate:
            if sys.platform == "darwin":
                schedule_macos_native_fullscreen_button(self)
            if self.isFullScreen() and self.isActiveWindow():
                QTimer.singleShot(0, self.restore_cinema_after_activation)
        return super().event(event)

    def changeEvent(self, event):
        super().changeEvent(event)
        if event.type() == QEvent.ActivationChange:
            if self.isActiveWindow() and self.isFullScreen():
                QTimer.singleShot(0, self.restore_cinema_after_activation)
            elif self.chrome_overlay_mode:
                self.cinema_timer.stop()
            return
        if event.type() != QEvent.WindowStateChange:
            return
        self.cinema_restore_last_state_change = time.monotonic()
        try:
            old_state = event.oldState()
        except Exception:
            old_state = Qt.WindowStates()
        debug_log(
            "response",
            "preview window state changed",
            old_state=str(old_state),
            new_state=str(self.windowState()),
            full=self.isFullScreen(),
            maximized=bool(self.windowState() & Qt.WindowMaximized),
            cinema=bool(self.property("cinema")),
            exiting=self.exiting_cinema,
            width=self.width(),
            height=self.height(),
        )
        state = self.windowState()
        full = bool(state & Qt.WindowFullScreen)
        maximized = bool(state & Qt.WindowMaximized)
        if sys.platform == "darwin" and maximized and not full and not self.exiting_cinema:
            if not bool(getattr(self, "_zoom_to_fullscreen_pending", False)):
                setattr(self, "_zoom_to_fullscreen_pending", True)
                self.capture_windowed_geometry_for_cinema()
                def _promote_preview_zoom():
                    try:
                        if self.isVisible():
                            # Never bounce through WindowNoState. Going maximized
                            # -> normal -> fullscreen produced the visible
                            # expand/contract/expand animation. Promote directly.
                            self.enter_cinema_mode()
                    finally:
                        QTimer.singleShot(900, lambda: setattr(self, "_zoom_to_fullscreen_pending", False))
                QTimer.singleShot(0, _promote_preview_zoom)
            return
        if self.exiting_cinema:
            # Native fullscreen owns the transition. The verifier observes it;
            # it must never bounce the state back and forth from this callback.
            if not full and not maximized:
                self.finish_cinema_ui_exit()
            self.cinema_restore_verify_timer.start(260)
            return
        if full:
            if not bool(self.property("cinema")):
                if self.windowed_geometry_before_cinema is None:
                    self.capture_windowed_geometry_for_cinema()
                if not self.cinema_entry_pending:
                    self.cinema_session_id += 1
                self.set_cinema_style(True)
            self.cinema_entry_pending = False
            self.fullscreen_btn.setText("Exit Full Screen")
            self.show_cinema_chrome(schedule_hide=self.media_is_playing())
            return
        if bool(self.property("cinema")):
            # The green button can end native fullscreen without passing through
            # exit_cinema_mode(). Adopt that transition instead of starting one.
            self.exit_cinema_mode(native_transition_started=True)
            return
        if promote_macos_zoom_to_fullscreen(
            self,
            event,
            self.enter_cinema_mode,
            self.capture_windowed_geometry_for_cinema,
        ):
            return
        if not maximized:
            self.cinema_entry_pending = False

    def sync_embedded_preview(self, path: Optional[Path], meta: Optional[MediaMeta] = None) -> None:
        panel = self.embedded_preview_panel
        begin = getattr(panel, "begin_external_preview", None)
        if callable(begin):
            try:
                begin(self, path, meta)
            except (AttributeError, RuntimeError) as exc:
                preview_trace(
                    "window",
                    "embedded ownership synchronization failed",
                    path,
                    force=True,
                    error=type(exc).__name__,
                )

    def effective_path(self) -> Optional[Path]:
        """Return the newest navigation target, including one still settling."""
        return self.queued_preview_path or self.current_path

    def cancel_queued_path(self, *, resume_current: bool) -> None:
        """Cancel a pending navigation load and optionally resume the retained row."""
        self.queued_path_timer.stop()
        had_pending = self.queued_preview_path is not None
        should_resume = bool(self.queued_transport_should_resume)
        self.queued_preview_path = None
        self.queued_preview_meta = None
        self.queued_transport_quiesced = False
        self.queued_transport_should_resume = False
        self.queued_path_started_at = 0.0
        self.queued_path_change_count = 0
        if not (had_pending and resume_current and self.current_path is not None):
            return
        if (
            should_resume
            and not self.playback_paused_by_user
            and not self.global_playback_lock_owners
            and self.media_player is not None
            and is_media_path(self.current_path)
        ):
            try:
                request_video_playback(self)
                self.apply_mute()
                self.media_player.play()
                self.set_dimmed(False)
                self.show_cinema_chrome(
                    schedule_hide=self.isFullScreen() and self.media_is_playing()
                )
            except (AttributeError, RuntimeError, TypeError):
                pass
        elif self.current_path is not None and is_media_path(self.current_path):
            self.set_dimmed(
                bool(self.playback_paused_by_user or self.global_playback_lock_owners)
            )

    def queue_path(
        self,
        path: Optional[Path],
        meta: Optional[MediaMeta] = None,
        *,
        delay_ms: int = 120,
    ) -> None:
        """Debounce row traversal so only its final media source is prepared."""
        if path is None:
            self.cancel_queued_path(resume_current=False)
            self.set_path(path, meta)
            return
        path = Path(path)
        if not path.exists():
            self.cancel_queued_path(resume_current=False)
            self.set_path(path, meta)
            return
        if path == self.current_path:
            if self.queued_preview_path is not None:
                self.cancel_queued_path(resume_current=True)
            return

        previous_pending = self.queued_preview_path
        same_pending = path == previous_pending
        if previous_pending is None:
            self.queued_path_started_at = time.monotonic()
            self.queued_path_change_count = 1
        elif not same_pending:
            self.queued_path_change_count += 1
        self.queued_preview_path = path
        self.queued_preview_meta = meta
        if not self.queued_transport_quiesced:
            self.cancel_auto_next_countdown()
            self.suppress_next_end_countdown = True
            self.stop_seek_hold()
            self.scrub_seeker.cancel()
            self.pending_media_seek_ms = None
            self.queued_transport_should_resume = bool(
                self.current_path is not None
                and is_media_path(self.current_path)
                and not self.playback_paused_by_user
                and not self.global_playback_lock_owners
            )
            if self.queued_transport_should_resume and self.media_player is not None:
                try:
                    # Pause retains the last frame and avoids the blank/zoom flash
                    # produced by a full stop while the user is still scrolling.
                    self.media_player.pause()
                except (AttributeError, RuntimeError):
                    pass
            self.queued_transport_quiesced = True
        if not same_pending or not self.queued_path_timer.isActive():
            self.queued_path_timer.start(max(40, int(delay_ms)))

    def apply_queued_path(self) -> None:
        path = self.queued_preview_path
        meta = self.queued_preview_meta
        started_at = self.queued_path_started_at
        change_count = self.queued_path_change_count
        self.queued_preview_path = None
        self.queued_preview_meta = None
        self.queued_transport_quiesced = False
        self.queued_transport_should_resume = False
        self.queued_path_started_at = 0.0
        self.queued_path_change_count = 0
        if path is not None:
            preview_trace(
                "window",
                "queued navigation settled",
                path,
                force=True,
                settle_ms=(
                    round((time.monotonic() - started_at) * 1000)
                    if started_at
                    else 0
                ),
                targets_seen=max(1, int(change_count)),
                superseded=max(0, int(change_count) - 1),
                decision="load newest requested preview only",
            )
            self.set_path(path, meta)

    def release_embedded_preview(self, restore: bool = True) -> None:
        panel = self.embedded_preview_panel
        end = getattr(panel, "end_external_preview", None)
        if callable(end):
            try:
                try:
                    end(self, restore=restore)
                except TypeError:
                    end(self)
            except (AttributeError, RuntimeError) as exc:
                preview_trace(
                    "window",
                    "embedded ownership release failed",
                    self.current_path,
                    force=True,
                    error=type(exc).__name__,
                )

    def set_path(self, path: Optional[Path], meta: Optional[MediaMeta] = None):
        if self.queued_preview_path is not None:
            self.cancel_queued_path(
                resume_current=bool(path is not None and Path(path) == self.current_path)
            )
        if not path or not path.exists():
            self.close()
            return

        same_path = self.current_path == path
        previous_kind = kind_for_path(self.current_path) if self.current_path else "none"
        self.interrupt_stale_preview_workers(path)
        self.cancel_auto_next_countdown()
        self.suppress_next_end_countdown = False
        self.current_path = path
        # The separate Preview owns the sole playback session even when it is
        # opened paused (or on an image/text row).  Ownership is independent
        # from whether this particular selection autoplays.
        request_video_playback(self)
        if meta is None and self.meta_provider:
            meta = self.meta_provider(path)
        if meta is None:
            cached_provider = getattr(
                self.embedded_preview_panel,
                "cached_media_metadata_if_ready",
                None,
            )
            if callable(cached_provider):
                meta = cached_provider(path)
        if meta is None:
            request_metadata = getattr(
                self.embedded_preview_panel,
                "request_media_metadata",
                None,
            )
            if callable(request_metadata):
                QTimer.singleShot(
                    0,
                    lambda requested_path=Path(path): request_metadata(requested_path)
                    if self.current_path == requested_path
                    else None,
                )
        self.sync_embedded_preview(path, meta)
        suffix = path.suffix.lower()
        debug_log(
            "response",
            "preview selection changed",
            force=True,
            previous_kind=previous_kind,
            media_kind=kind_for_path(path),
            same_item=same_path,
            full=self.isFullScreen(),
            cinema=bool(self.property("cinema")),
            width=self.width(),
            height=self.height(),
        )
        if meta is None:
            meta = MediaMeta()
        self.current_media_meta = meta
        if not same_path:
            self.reset_media_timeline(meta)
        info = file_info(path)
        self.title_label.setText(path.name)
        self.title_label.setToolTip(str(path))
        bits = [kind_for_path(path)]
        if meta.duration:
            bits.append(meta.duration)
        if meta.resolution:
            bits.append(meta.resolution)
        if meta.sample_rate:
            bits.append(meta.sample_rate)
        if info:
            bits.append(human_size(info.size))
        self.meta_label.setText("  |  ".join(bits))

        if is_video_path(path):
            if preview_requires_compatibility_proxy(path, meta):
                decision = "buffered compatibility playback required by codec policy"
                source_kind = "compatibility proxy"
            else:
                decision = "direct Qt playback with no-frame watchdog"
                source_kind = "original media"
        elif suffix in AUDIO_EXTS:
            decision = "direct Qt audio playback"
            source_kind = "original media"
        elif suffix in IMAGE_EXTS:
            decision = "image artwork"
            source_kind = "static artwork"
        elif suffix in CODE_EXTS or suffix in {".txt", ".md", ".csv", ".json", ".xml", ".yaml", ".yml", ".toml", ".rtf"}:
            decision = "text preview"
            source_kind = "static text"
        else:
            decision = "static file artwork"
            source_kind = "static artwork"
        self._debug_media_descriptor = media_preview_descriptor(path, meta, info)
        preview_trace(
            "window",
            "preview source decision",
            path,
            force=True,
            decision=decision,
            source_kind=source_kind,
            logical_paused=bool(self.playback_paused_by_user),
            **self._debug_media_descriptor,
        )

        if same_path:
            if (
                is_video_path(path)
                and preview_requires_compatibility_proxy(path, meta)
                and not self.playing_compatibility_proxy
                and not preview_proxy_running(self.playable_proxy_workers, path)
            ):
                self.start_compatible_media_preview(path)
            return

        if is_media_path(path):
            if is_video_path(path) and preview_requires_compatibility_proxy(path, meta):
                self.start_compatible_media_preview(path)
            else:
                self.show_media(path, is_video_path(path))
        elif suffix in IMAGE_EXTS:
            self.show_artwork_async(path)
        elif suffix in CODE_EXTS or suffix in {".txt", ".md", ".csv", ".json", ".xml", ".yaml", ".yml", ".toml", ".rtf"}:
            self.show_text(path)
        else:
            self.show_artwork_async(path)

    @staticmethod
    def metadata_duration(meta: Optional[MediaMeta]) -> int:
        return media_meta_duration_ms(meta)

    def reset_media_timeline(self, meta: Optional[MediaMeta] = None):
        """Clear the previous row's range before any new source can load."""
        self._proxy_rebind_generation += 1
        self._proxy_rebind_pending = False
        self._provisional_resume_position_ms = 0
        self.scrub_seeker.cancel()
        self.pending_media_seek_ms = None
        self.metadata_duration_ms = self.metadata_duration(meta)
        self.media_duration_ms = self.metadata_duration_ms
        self.scrub_slider.setRange(0, self.media_duration_ms)
        self.scrub_slider.setValue(0)
        self.update_time_label(0)

    def on_external_metadata_loaded(self, path: Path, meta: MediaMeta):
        """Apply the embedded panel's background probe without reloading media."""
        if Path(path) != self.current_path:
            return
        self.current_media_meta = meta or MediaMeta()
        self.metadata_duration_ms = self.metadata_duration(self.current_media_meta)
        if self.metadata_duration_ms > self.media_duration_ms:
            self.media_duration_ms = self.metadata_duration_ms
            self.scrub_slider.setRange(0, self.media_duration_ms)
            self.update_time_label(self.scrub_slider.value())
        info = file_info(path)
        bits = [kind_for_path(path)]
        if self.current_media_meta.duration:
            bits.append(self.current_media_meta.duration)
        if self.current_media_meta.resolution:
            bits.append(self.current_media_meta.resolution)
        if self.current_media_meta.sample_rate:
            bits.append(self.current_media_meta.sample_rate)
        if info:
            bits.append(human_size(info.size))
        self.meta_label.setText("  |  ".join(bits))

    def media_source_ready_for_seek(self, target: Optional[int] = None) -> bool:
        if self.media_player is None:
            return False
        if (
            self.playable_proxy_source is not None
            and self.current_path is not None
            and self.playable_proxy_source == self.current_path
            and not self.playing_compatibility_proxy
        ):
            return False
        source_provider = getattr(self.media_player, "source", None)
        if not callable(source_provider):
            # Lightweight test/alternate players do not expose QUrl source().
            return True
        try:
            source = source_provider()
            if source is None or source.isEmpty():
                return False
        except (AttributeError, RuntimeError, TypeError):
            return False
        if target is None or int(target) <= 0:
            return True
        available_duration = preview_player_duration_ms(self.media_player)
        if available_duration <= 0:
            return False
        return not (
            self.playing_compatibility_proxy
            and int(target) > available_duration
        )

    def apply_pending_media_seek(self):
        pending = self.pending_media_seek_ms
        if pending is None or not self.media_source_ready_for_seek(pending):
            return
        try:
            available_duration = preview_player_duration_ms(
                self.media_player,
                self.media_duration_ms,
            )
        except (AttributeError, RuntimeError, TypeError, ValueError):
            available_duration = self.media_duration_ms
        if available_duration <= 0:
            return
        # A progressive proxy may initially expose only its first buffered
        # segment. Keep a farther seek pending until a longer/final source is
        # rebound instead of silently clamping it to the segment edge.
        if self.playing_compatibility_proxy and pending > available_duration:
            return
        self.pending_media_seek_ms = None
        target = max(0, min(available_duration, int(pending)))
        self.scrub_seeker.commit(target, reason="deferred user seek")
        self.scrub_slider.setValue(target)
        self.update_time_label(target)
        if (
            not self.playback_paused_by_user
            and not self.global_playback_lock_owners
            and QMediaPlayer is not None
            and self.media_player.playbackState() != QMediaPlayer.PlaybackState.PlayingState
        ):
            request_video_playback(self)
            self.media_player.play()
        preview_trace(
            "window",
            "deferred user seek applied",
            self.current_path,
            force=True,
            request_id=self.playable_proxy_request_id,
            source_kind=preview_source_kind(self),
            requested_position_ms=int(pending),
            actual_position_ms=target,
            available_duration_ms=available_duration,
        )

    def show_placeholder(self, text: str):
        self.cancel_auto_next_countdown()
        self.set_media_controls_available(False)
        self.show_cinema_chrome()
        self.stop_media()
        self.placeholder.setText(text)
        self.stack.setCurrentWidget(self.placeholder)
        self.media_duration_ms = 0
        self.update_time_label(0)

    def show_text(self, path: Path):
        self.cancel_auto_next_countdown()
        self.set_media_controls_available(False)
        self.show_cinema_chrome()
        self.stop_media()
        self.thumbnail_request_id += 1
        request_id = self.thumbnail_request_id
        self.placeholder.setText("Loading preview")
        self.stack.setCurrentWidget(self.placeholder)
        self.media_duration_ms = 0
        self.update_time_label(0)
        worker = PreviewTextWorker(request_id, path)
        self.text_workers.append(worker)
        worker.loaded.connect(self.on_text_loaded)
        worker.failed.connect(self.on_text_failed)
        worker.finished.connect(lambda worker=worker: self.cleanup_text_worker(worker))
        worker.start()

    def on_text_loaded(self, request_id: int, path: Path, preview_text: str):
        if request_id != self.thumbnail_request_id or path != self.current_path:
            return
        self.text_view.setPlainText(preview_text or "No text preview")
        self.stack.setCurrentWidget(self.text_view)

    def on_text_failed(self, request_id: int, path: Path):
        if request_id == self.thumbnail_request_id and path == self.current_path:
            self.placeholder.setText("No text preview")
            self.stack.setCurrentWidget(self.placeholder)

    def cleanup_text_worker(self, worker: PreviewTextWorker):
        if worker in self.text_workers:
            self.text_workers.remove(worker)
        worker.deleteLater()

    def display_media_artwork(self, pixmap: QPixmap, fallback: str):
        if self.video_widget is not None and self.current_path and is_video_path(self.current_path):
            self.video_widget.set_poster_pixmap(pixmap)
        if pixmap.isNull():
            self.placeholder.setText(fallback)
            if self.stack.currentWidget() is not self.video_widget:
                self.stack.setCurrentWidget(self.placeholder)
            return
        self.image_label.setPixmap(pixmap)
        if self.stack.currentWidget() is not self.video_widget:
            self.stack.setCurrentWidget(self.image_label)

    def show_artwork_async(self, path: Path):
        self.cancel_auto_next_countdown()
        self.set_media_controls_available(False)
        self.show_cinema_chrome()
        self.stop_media()
        self.start_media_artwork_thumbnail(path)

    def start_media_artwork_thumbnail(self, path: Path):
        for worker in list(self.thumbnail_workers):
            if getattr(worker, "path", None) == path:
                continue
            try:
                if worker.isRunning():
                    worker.cancel()
            except RuntimeError:
                pass
        self.thumbnail_request_id += 1
        request_id = self.thumbnail_request_id
        self.placeholder.setText("Loading preview")
        if self.stack.currentWidget() is not self.video_widget:
            self.stack.setCurrentWidget(self.placeholder)
        worker = PreviewThumbnailWorker(request_id, path)
        self.thumbnail_workers.append(worker)
        worker.loaded.connect(self.on_media_artwork_loaded)
        worker.failed.connect(self.on_media_artwork_failed)
        worker.finished.connect(lambda worker=worker: self.cleanup_thumbnail_worker(worker))
        worker.start()

    def schedule_video_artwork_fallback(self, path: Path, delay_ms: int = 5000):
        self.cancel_video_artwork_fallback(cancel_worker=True)
        # Invalidate artwork from the previous row immediately. A working video
        # sink will provide the poster itself, avoiding a second FFmpeg decode.
        self.thumbnail_request_id += 1
        self.pending_video_poster_path = path
        self.video_poster_timer.start(max(0, int(delay_ms)))

    def on_video_frame_conversion_unavailable(self, reason: str):
        if self.media_player is None or self.video_widget is None or self.current_path is None:
            return
        if not is_video_path(self.current_path):
            return
        preview_trace(
            "window",
            "video frame conversion unavailable",
            self.current_path,
            force=True,
            request_id=self.playable_proxy_request_id,
            source_kind=preview_source_kind(self),
            decision="route through compatibility recovery",
            backend_message=_clean_process_diagnostic(reason, self.current_path, limit=500),
            has_frame=bool(self.video_widget.has_frame()),
            **video_frame_snapshot(self.video_widget),
            **qmedia_player_snapshot(self.media_player),
        )
        if self.playing_compatibility_proxy:
            self.fallback_from_unpaintable_media_proxy(
                Path(self.current_path),
                reason,
            )
            return
        if self.current_path.suffix.lower() == ".webm":
            path = Path(self.current_path)
            if not preview_proxy_running(self.playable_proxy_workers, path):
                QTimer.singleShot(
                    0,
                    lambda failed_path=path: self.start_compatible_media_preview(failed_path)
                    if self.current_path == failed_path else None,
                )
            return
        if self.video_widget.activate_native_fallback(self.media_player, reason):
            self.cancel_video_artwork_fallback(cancel_worker=True)
            self.stack.setCurrentWidget(self.video_widget)
            return
        path = Path(self.current_path)
        QTimer.singleShot(
            0,
            lambda failed_path=path: self.start_compatible_media_preview(failed_path)
            if self.current_path == failed_path else None,
        )

    def start_pending_video_artwork(self):
        path = self.pending_video_poster_path
        self.pending_video_poster_path = None
        if (
            path is None
            or path != self.current_path
            or self.video_widget is None
            or self.video_widget.has_frame()
            or self.video_widget.using_native_fallback()
        ):
            return
        preview_trace(
            "window",
            "no-frame watchdog expired",
            path,
            force=True,
            request_id=self.playable_proxy_request_id,
            source_kind=preview_source_kind(self),
            decision="evaluate proxy/native/poster recovery",
            has_frame=False,
            has_poster=bool(getattr(self.video_widget, "_poster_image", None) is not None),
            **video_frame_snapshot(self.video_widget),
            **qmedia_player_snapshot(self.media_player),
        )
        if is_video_path(path):
            if self.playing_compatibility_proxy:
                self.fallback_from_unpaintable_media_proxy(
                    Path(path),
                    "no paintable frame arrived from the compatibility proxy",
                )
                return
            if path.suffix.lower() == ".webm":
                self.start_compatible_media_preview(path)
                return
            if self.video_widget.activate_native_fallback(self.media_player, "no convertible frame after loading"):
                return
            self.start_compatible_media_preview(path)
            return
        self.start_media_artwork_thumbnail(path)

    def cancel_video_artwork_fallback(self, cancel_worker: bool = False):
        self.video_poster_timer.stop()
        path = self.pending_video_poster_path
        self.pending_video_poster_path = None
        if not cancel_worker:
            return
        path = path or self.current_path
        for worker in list(self.thumbnail_workers):
            if path is not None and getattr(worker, "path", None) != path:
                continue
            try:
                if worker.isRunning():
                    worker.cancel()
            except RuntimeError:
                pass

    def on_video_first_frame_ready(self):
        frame_key = (
            preview_item_id(self.current_path),
            self.playable_proxy_request_id,
            preview_source_kind(self),
        )
        if self._debug_first_frame_key != frame_key:
            self._debug_first_frame_key = frame_key
            image = getattr(self.video_widget, "_frame_image", None)
            try:
                frame_width = int(image.width()) if image is not None else 0
                frame_height = int(image.height()) if image is not None else 0
                pixel_format = qt_enum_name(image.format()) if image is not None else "unknown"
            except (AttributeError, RuntimeError, TypeError, ValueError):
                frame_width = 0
                frame_height = 0
                pixel_format = "unknown"
            preview_trace(
                "window",
                "first paintable video frame",
                self.current_path,
                force=True,
                request_id=self.playable_proxy_request_id,
                source_kind=preview_source_kind(self),
                decision="video widget now has visible media",
                frame_width=frame_width,
                frame_height=frame_height,
                pixel_format=pixel_format,
                elapsed_ms=(
                    round((time.monotonic() - self._debug_source_started_at) * 1000)
                    if self._debug_source_started_at > 0.0
                    else 0
                ),
                logical_paused=bool(self.playback_paused_by_user),
                **video_frame_snapshot(self.video_widget),
                **qmedia_player_snapshot(self.media_player),
            )
        self.cancel_video_artwork_fallback(cancel_worker=True)
        # A relayed poster can arrive after the proxy source was bound but before
        # its first decoded frame.  The poster is stored on the video widget, so
        # make that surface authoritative as soon as a real frame arrives instead
        # of leaving a stale image-label page covering playback.
        if (
            self.video_widget is not None
            and self.current_path is not None
            and is_video_path(self.current_path)
        ):
            self.stack.setCurrentWidget(self.video_widget)
        if self.priming_paused_frame:
            self.priming_paused_frame = False
            try:
                self.media_player.pause()
            except (AttributeError, RuntimeError):
                pass
            self.apply_mute()
            self.set_dimmed(True)

    def prime_current_paused_video_frame(self):
        """Decode one silent frame, then keep the new selection visibly paused."""
        if self.media_player is None:
            self.set_dimmed(True)
            return
        self.priming_paused_frame = True
        if self.audio_output is not None:
            try:
                self.audio_output.setMuted(True)
            except (AttributeError, RuntimeError):
                pass
        try:
            self.media_player.play()
        except (AttributeError, RuntimeError):
            self.priming_paused_frame = False
            self.apply_mute()
        self.set_dimmed(True)

    def on_media_artwork_loaded(self, request_id: int, data: bytes):
        if request_id != self.thumbnail_request_id:
            return
        pixmap = QPixmap()
        pixmap.loadFromData(data)
        self.display_media_artwork(pixmap, kind_for_path(self.current_path) if self.current_path else "Media")

    def on_media_artwork_failed(self, request_id: int):
        if request_id == self.thumbnail_request_id:
            self.display_media_artwork(QPixmap(), kind_for_path(self.current_path) if self.current_path else "Media")

    def cleanup_thumbnail_worker(self, worker: PreviewThumbnailWorker):
        if worker in self.thumbnail_workers:
            self.thumbnail_workers.remove(worker)
        worker.deleteLater()

    def start_compatible_media_preview(self, path: Path):
        """Keep artwork visible while preparing a playable large-preview proxy."""
        if (
            (
                self.playing_compatibility_proxy
                and self.playable_proxy_source == path
            )
            or preview_proxy_running(self.playable_proxy_workers, path)
        ):
            return
        preview_trace(
            "window",
            "compatibility proxy requested",
            path,
            force=True,
            video_codec=container_video_codec_hint(path) or "metadata",
            decision="bypass Qt decoder and prepare compatible H.264/AAC source",
            source_kind="original media pending proxy",
            logical_paused=bool(self.playback_paused_by_user),
        )
        self.start_playable_proxy_media(path)
        # The compatibility worker is already decoding this source. Starting a
        # second FFmpeg process merely to obtain a poster doubles cold-start I/O
        # and decode pressure for large AV1/VP9 media. Failure/watchdog paths
        # still request artwork when it is actually needed.

    def accept_shared_compatibility_proxy(
        self,
        source_path: Path,
        proxy_path: str,
    ) -> bool:
        """Consume the paired embedded panel's progressive proxy stream."""
        source_path = Path(source_path)
        candidate = Path(proxy_path)
        if (
            self.current_path != source_path
            or self.playable_proxy_source != source_path
            or self.embedded_preview_panel is None
        ):
            return False
        # FFmpeg atomically renames the progressive path on completion. A
        # queued provisional signal can therefore arrive after that pathname
        # disappeared; the retained waiter will deliver the final cache.
        if not candidate.exists():
            return False
        self.on_playable_proxy_media_ready(
            self.playable_proxy_request_id,
            str(candidate),
        )
        return self.bound_compatibility_proxy_path == candidate

    def accept_shared_preview_poster(
        self,
        source_path: Path,
        pixmap: QPixmap,
    ) -> bool:
        """Display the paired embedded panel's poster during a cold conversion."""
        source_path = Path(source_path)
        if (
            self.current_path != source_path
            or self.embedded_preview_panel is None
            or pixmap.isNull()
        ):
            return False
        # Do not replace a proxy that has already produced a real video frame.
        if (
            self.stack.currentWidget() is self.video_widget
            and self.video_widget is not None
            and self.video_widget.has_frame()
        ):
            return True
        if (
            self.playing_compatibility_proxy
            and self.bound_compatibility_proxy_path is not None
            and self.video_widget is not None
        ):
            # Keep the bound playback surface on top. FrameVideoWidget paints
            # this poster until the first decoded frame replaces it.
            self.video_widget.set_poster_pixmap(pixmap)
            self.stack.setCurrentWidget(self.video_widget)
        else:
            self.display_media_artwork(pixmap, "Video")
        self.set_dimmed(bool(self.playback_paused_by_user or self.global_playback_lock_owners))
        preview_trace(
            "window",
            "shared preview poster accepted",
            source_path,
            force=True,
            request_id=self.playable_proxy_request_id,
            source_kind="shared extracted poster",
            decision="show immediate visual while compatibility source prepares",
        )
        return True

    def accept_shared_compatibility_proxy_buffer(
        self,
        source_path: Path,
        proxy_path: str,
        buffered_duration_ms: int,
    ) -> bool:
        """Apply growth updates only to the shared temporary now on screen."""
        source_path = Path(source_path)
        candidate = Path(proxy_path)
        if (
            self.current_path != source_path
            or self.playable_proxy_source != source_path
            or self.bound_compatibility_proxy_path != candidate
            or not self.playing_compatibility_proxy
        ):
            return False
        self.on_playable_proxy_media_buffer_extended(
            self.playable_proxy_request_id,
            str(candidate),
            max(0, int(buffered_duration_ms)),
        )
        return True

    def start_playable_proxy_media(self, path: Path):
        # Treat proxy preparation as the playback source transition itself. Stop
        # the previous row immediately so its audio/frame cannot linger while the
        # AV1 proxy is being prepared. Controls stay available for the new video.
        self.cancel_video_artwork_fallback(cancel_worker=True)
        self.priming_paused_frame = False
        self.set_media_controls_available(True)
        if self.media_player is not None:
            try:
                self.media_player.stop()
                self.media_player.setSource(QUrl())
            except Exception:
                pass
        # The previous row is no longer the active audio source while FFmpeg
        # prepares a compatibility file. Stop its health timer and counters so
        # diagnostics cannot report stale decoded audio for this new row.
        reset_preview_audio_monitor(self)
        if self.video_widget is not None:
            self.video_widget.clear_frame(clear_poster=True)
        self.playable_proxy_request_id += 1
        request_id = self.playable_proxy_request_id
        self._proxy_rebind_generation += 1
        self._proxy_rebind_pending = False
        self._provisional_resume_position_ms = 0
        self.playable_proxy_source = Path(path)
        self.playing_compatibility_proxy = False
        self.bound_compatibility_proxy_path = None
        self.awaiting_final_proxy = False
        self._debug_source_started_at = time.monotonic()
        for worker in list(self.playable_proxy_workers):
            try:
                worker.cancel()
            except RuntimeError:
                pass
        self.placeholder.setText("Preparing compatible video preview…")
        self.stack.setCurrentWidget(self.placeholder)
        self.set_dimmed(bool(self.playback_paused_by_user or self.global_playback_lock_owners))
        preview_trace(
            "window",
            "proxy worker started",
            path,
            force=True,
            request_id=request_id,
            source_kind="proxy worker",
            decision="background conversion or cache validation",
            logical_paused=bool(self.playback_paused_by_user),
        )
        worker = PreviewPlayableProxyWorker(request_id, path, surface="window")
        self.playable_proxy_workers.append(worker)
        worker.ready.connect(self.on_playable_proxy_media_ready)
        worker.bufferExtended.connect(self.on_playable_proxy_media_buffer_extended)
        worker.finalized.connect(self.on_playable_proxy_media_finalized)
        worker.failed.connect(self.on_playable_proxy_media_failed)
        worker.progress.connect(self.on_playable_proxy_media_progress)
        worker.finished.connect(lambda w=worker: self.cleanup_playable_proxy_media_worker(w))
        worker.start()

    def on_playable_proxy_media_progress(self, request_id: int, message: str):
        if request_id != self.playable_proxy_request_id:
            return
        if self.current_path != self.playable_proxy_source:
            return
        if (
            self.playing_compatibility_proxy
            and self.bound_compatibility_proxy_path is not None
        ):
            # The retained window worker may still be waiting on the embedded
            # producer's lock. Its status text must not replace a progressive
            # video frame that is already playing in this window.
            return
        self.placeholder.setText(message)
        poster = getattr(self.image_label, "_source_pixmap", None)
        has_poster = poster is not None and not poster.isNull()
        if not has_poster:
            self.stack.setCurrentWidget(self.placeholder)
        self.set_dimmed(bool(self.playback_paused_by_user or self.global_playback_lock_owners))
        preview_trace(
            "window",
            "proxy preparation progress",
            self.current_path,
            request_id=request_id,
            source_kind="proxy worker",
            decision=message,
            has_poster=has_poster,
        )

    def on_playable_proxy_media_ready(self, request_id: int, proxy_path: str):
        if request_id != self.playable_proxy_request_id or self.current_path != self.playable_proxy_source:
            return
        if self.media_player is None or self.video_widget is None:
            return
        candidate = Path(proxy_path)
        if not candidate.exists():
            return
        bound = self.bound_compatibility_proxy_path
        if bound == candidate and self.playing_compatibility_proxy:
            return
        if (
            bound is not None
            and bound.name.startswith(".")
            and not candidate.name.startswith(".")
            and (self.playing_compatibility_proxy or self.awaiting_final_proxy)
        ):
            # Either the embedded producer or this window's retained waiter can
            # announce the completed cache first. Treat the first announcement
            # as finalization; the second becomes a no-op instead of restarting
            # playback at zero.
            self.on_playable_proxy_media_finalized(request_id, str(candidate))
            return
        self.awaiting_final_proxy = Path(proxy_path).name.startswith(".")
        proxy_source_kind = (
            "growing compatibility proxy"
            if self.awaiting_final_proxy
            else "validated compatibility proxy"
        )
        # Preserve the extracted artwork until the first proxy frame paints.
        self.video_widget.clear_frame(clear_poster=False)
        self.stack.setCurrentWidget(self.video_widget)
        self.playback_recovery_source = None
        self.media_player.stop()
        self.video_widget.reset_player_output(self.media_player)
        self.playing_compatibility_proxy = True
        self.bound_compatibility_proxy_path = candidate
        self._proxy_rebind_pending = False
        reset_preview_audio_monitor(self)
        self.media_player.setSource(QUrl.fromLocalFile(proxy_path))
        preview_trace(
            "window",
            "Qt playback source assigned",
            self.current_path,
            force=True,
            request_id=request_id,
            source_kind=proxy_source_kind,
            decision="proxy ready; bind to QMediaPlayer/QVideoSink",
            elapsed_ms=round((time.monotonic() - self._debug_source_started_at) * 1000),
        )
        # Keep the source metadata's full timeline while Qt initially sees only
        # the first progressive segment. A seek made during preparation remains
        # visible and will be committed once that position is buffered.
        self.media_duration_ms = max(self.media_duration_ms, self.metadata_duration_ms)
        self.scrub_slider.setRange(0, self.media_duration_ms)
        visible_position = max(0, int(self.pending_media_seek_ms or 0))
        if self.media_duration_ms > 0:
            visible_position = min(self.media_duration_ms, visible_position)
        self.scrub_slider.setValue(visible_position)
        self.update_time_label(visible_position)
        self.apply_mute()
        locked_by_other_window = bool(self.global_playback_lock_owners)
        if locked_by_other_window:
            # The source may finish buffering behind another Preview. Keep it
            # loaded but silent; release_large_preview restores the transport.
            self.set_dimmed(True)
            self.show_cinema_chrome()
        elif self.playback_paused_by_user:
            self.prime_current_paused_video_frame()
            self.show_cinema_chrome()
        else:
            request_video_playback(self)
            self.media_player.play()
            self.set_dimmed(False)
            self.show_cinema_chrome(schedule_hide=self.isFullScreen())
        self.schedule_video_artwork_fallback(self.current_path, delay_ms=5000)
        should_play = not self.playback_paused_by_user and not locked_by_other_window
        preview_trace(
            "window",
            "proxy playback requested",
            self.current_path,
            force=True,
            request_id=request_id,
            source_kind=proxy_source_kind,
            decision=(
                "play"
                if should_play
                else (
                    "remain silent behind another Preview window"
                    if locked_by_other_window
                    else "decode one frame then remain paused"
                )
            ),
            logical_paused=not should_play,
        )

    def _rebind_playable_proxy_media_source(
        self,
        request_id: int,
        proxy_path: str,
        *,
        decision: str,
        force: bool = False,
    ):
        if (
            request_id != self.playable_proxy_request_id
            or self.current_path != self.playable_proxy_source
            or not self.playing_compatibility_proxy
            or self.media_player is None
            or self.video_widget is None
        ):
            return
        if bool(getattr(self, "_proxy_rebind_pending", False)) and not force:
            return
        self._proxy_rebind_pending = True
        self._proxy_rebind_generation += 1
        rebind_generation = self._proxy_rebind_generation
        backend_position = preview_player_position_ms(self.media_player)
        pending_position = self.pending_media_seek_ms
        resume_position = max(
            backend_position,
            max(0, int(self._provisional_resume_position_ms)),
        )
        position = max(
            0,
            int(
                pending_position
                if pending_position is not None
                else self.scrub_seeker.preferred_position(resume_position)
            ),
        )
        seek_revision = None
        if pending_position is None:
            seek_revision = self.scrub_seeker.claim(
                position,
                reason="compatibility proxy rebind",
                timeout_ms=5000,
            )
        autoplay = bool(
            pending_position is None
            and not self.playback_paused_by_user
            and not self.global_playback_lock_owners
        )
        # Retain the currently painted frame across the very short source
        # rebind so fullscreen and embedded previews do not blink black.
        self.media_player.stop()
        self.media_player.setSource(QUrl())
        self.video_widget.reset_player_output(self.media_player)
        reset_preview_audio_monitor(self)
        self.media_player.setSource(QUrl.fromLocalFile(proxy_path))
        self.bound_compatibility_proxy_path = Path(proxy_path)
        if seek_revision is not None:
            self.scrub_seeker.apply_claim(seek_revision, position)
        self.apply_mute()
        if pending_position is not None:
            self.scrub_slider.setValue(position)
            self.update_time_label(position)
            self.apply_pending_media_seek()
        elif autoplay:
            request_video_playback(self)
            self.media_player.play()
            self.set_dimmed(False)
        elif not self.global_playback_lock_owners:
            self.prime_current_paused_video_frame()
        else:
            self.set_dimmed(True)
        if not Path(proxy_path).name.startswith("."):
            self._provisional_resume_position_ms = 0
        QTimer.singleShot(
            80,
            lambda rid=request_id, generation=rebind_generation, revision=seek_revision, pos=position: self.scrub_seeker.reapply_if_current(revision, pos)
            if revision is not None
            and rid == self.playable_proxy_request_id
            and generation == self._proxy_rebind_generation
            and self.current_path == self.playable_proxy_source
            and self.media_player is not None
            else None,
        )
        QTimer.singleShot(
            350,
            lambda rid=request_id, generation=rebind_generation: setattr(self, "_proxy_rebind_pending", False)
            if rid == self.playable_proxy_request_id
            and generation == self._proxy_rebind_generation
            else None,
        )
        preview_trace(
            "window",
            "buffered proxy source rebound",
            self.current_path,
            force=True,
            request_id=request_id,
            source_kind=(
                "growing compatibility proxy"
                if Path(proxy_path).name.startswith(".")
                else "validated compatibility proxy"
            ),
            decision=decision,
            position_ms=position,
            logical_paused=not autoplay,
        )

    def on_playable_proxy_media_buffer_extended(
        self,
        request_id: int,
        proxy_path: str,
        buffered_duration_ms: int,
    ):
        if (
            request_id != self.playable_proxy_request_id
            or self.current_path != self.playable_proxy_source
            or not self.playing_compatibility_proxy
            or self.media_player is None
            or self.bound_compatibility_proxy_path != Path(proxy_path)
        ):
            return
        known_duration = max(0, int(self.media_player.duration()))
        position = max(0, int(self.media_player.position()))
        pending_position = self.pending_media_seek_ms
        if pending_position is not None:
            if buffered_duration_ms < pending_position:
                return
            should_rebind = True
        else:
            if known_duration <= 0 or buffered_duration_ms <= known_duration + 3000:
                return
            if self.playback_paused_by_user:
                # With no pending seek, a paused transport can wait for the
                # finalized proxy instead of repeatedly rebuilding Qt's source.
                return
            should_rebind = known_duration - position <= 5000
        if should_rebind:
            self._rebind_playable_proxy_media_source(
                request_id,
                proxy_path,
                decision="refresh growing stream duration before playhead reaches buffered edge",
            )

    def on_playable_proxy_media_finalized(self, request_id: int, proxy_path: str):
        """Rebind a buffered window preview to the completed seekable cache."""
        if request_id != self.playable_proxy_request_id or self.current_path != self.playable_proxy_source:
            return
        candidate = Path(proxy_path)
        if (
            self.bound_compatibility_proxy_path == candidate
            and not self.awaiting_final_proxy
        ):
            return
        if (
            self.awaiting_final_proxy
            and not self.playing_compatibility_proxy
        ):
            # A provisional transport stream can fail Qt's early paintability
            # watchdog even though its finalized cache is healthy. Bind the
            # completed file as a fresh source rather than marooning this row on
            # artwork until the user selects it again.
            self.awaiting_final_proxy = False
            self.on_playable_proxy_media_ready(request_id, proxy_path)
            return
        self.awaiting_final_proxy = False
        self._rebind_playable_proxy_media_source(
            request_id,
            proxy_path,
            decision="preserve position and playback intent on finalized cache",
            force=True,
        )

    def on_playable_proxy_media_failed(self, request_id: int):
        if request_id != self.playable_proxy_request_id or self.current_path != self.playable_proxy_source:
            return
        if (
            self.playing_compatibility_proxy
            and self.bound_compatibility_proxy_path is not None
        ):
            # A retained lock waiter is only a recovery path. If its timeout or
            # retry fails after the paired producer already supplied playable
            # media, keep that media on screen and let its own watchdog decide.
            return
        preview_trace(
            "window",
            "compatibility proxy failed",
            self.current_path,
            force=True,
            request_id=request_id,
            source_kind="proxy worker",
            decision="show extracted poster; see media-proxy failure",
        )
        self.playing_compatibility_proxy = False
        self.bound_compatibility_proxy_path = None
        self.awaiting_final_proxy = False
        if self.media_player is not None:
            try:
                self.media_player.stop()
                self.media_player.setSource(QUrl())
            except (AttributeError, RuntimeError):
                pass
        reset_preview_audio_monitor(self)
        self.start_media_artwork_thumbnail(self.current_path)

    def cleanup_playable_proxy_media_worker(self, worker):
        if worker in self.playable_proxy_workers:
            self.playable_proxy_workers.remove(worker)
        worker.deleteLater()

    def show_media(self, path: Path, has_video: bool):
        if self.media_player is None:
            self.show_artwork_async(path)
            return
        self._proxy_rebind_generation += 1
        self._proxy_rebind_pending = False
        self._provisional_resume_position_ms = 0
        autoplay = not self.playback_paused_by_user
        request_video_playback(self)
        self.set_media_controls_available(True)
        self.thumbnail_request_id += 1
        if has_video and self.video_widget is not None:
            self.video_widget.clear_frame(clear_poster=True)
            self.stack.setCurrentWidget(self.video_widget)
        else:
            self.cancel_video_artwork_fallback(cancel_worker=True)
            self.start_media_artwork_thumbnail(path)
        self.media_duration_ms = self.metadata_duration_ms
        self.scrub_slider.setRange(0, self.media_duration_ms)
        self.scrub_slider.setValue(0)
        self.update_time_label(0)
        self.playback_recovery_source = None
        self.priming_paused_frame = False
        self._debug_source_started_at = time.monotonic()
        self.media_player.stop()
        if has_video and self.video_widget is not None:
            self.video_widget.reset_player_output(self.media_player)
        self.playing_compatibility_proxy = False
        self.bound_compatibility_proxy_path = None
        self.awaiting_final_proxy = False
        if has_video:
            self.playback_recovery_source = Path(path)
        reset_preview_audio_monitor(self)
        self.media_player.setSource(QUrl.fromLocalFile(str(path)))
        preview_trace(
            "window",
            "Qt playback source assigned",
            path,
            force=True,
            request_id=self.playable_proxy_request_id,
            source_kind="original media" if has_video else "original audio",
            decision="direct QMediaPlayer/QVideoSink playback" if has_video else "direct audio playback",
            logical_paused=not autoplay,
        )
        self.apply_mute()
        if autoplay:
            self.media_player.play()
            self.set_dimmed(False)
        elif has_video:
            self.prime_current_paused_video_frame()
        else:
            # Audio-only selections have no firstFrameReady signal.  Priming
            # them would silently play forever while waiting for a video frame.
            self.priming_paused_frame = False
            self.media_player.pause()
            self.apply_mute()
            self.set_dimmed(True)
        if has_video and self.video_widget is not None:
            fallback_delay = preview_direct_watchdog_delay_ms(
                path,
                autoplay=autoplay,
            )
            self.schedule_video_artwork_fallback(path, fallback_delay)
        self.show_cinema_chrome(schedule_hide=self.isFullScreen() and autoplay)

    def on_video_playback_error(self, error, detail: str = ""):
        path = self.current_path
        backend_message = _clean_process_diagnostic(
            detail or (self.media_player.errorString() if self.media_player else ""),
            path,
            limit=900,
        )
        error_name = qt_enum_name(error)
        error_signature = (
            preview_item_id(path),
            self.playable_proxy_request_id,
            preview_source_kind(self),
            error_name,
            backend_message,
        )
        if self._debug_last_error_signature != error_signature:
            self._debug_last_error_signature = error_signature
            preview_trace(
                "window",
                "Qt playback error",
                path,
                force=True,
                request_id=self.playable_proxy_request_id,
                source_kind=preview_source_kind(self),
                error=error_name,
                error_code=str(error),
                backend_message=backend_message,
                **qmedia_player_snapshot(self.media_player),
            )
        if path is None or not is_video_path(path):
            return
        if self.playing_compatibility_proxy:
            QTimer.singleShot(
                0,
                lambda failed_path=Path(path): self.fallback_from_unpaintable_media_proxy(
                    failed_path,
                    "Qt rejected the compatibility proxy",
                ),
            )
            return
        if self.playback_recovery_source != path:
            return
        if preview_proxy_running(self.playable_proxy_workers, path):
            return
        self.playback_recovery_source = None
        QTimer.singleShot(0, lambda failed_path=path: self.recover_video_playback(failed_path))

    def recover_video_playback(self, failed_path: Path):
        if self.current_path != failed_path or self.playing_compatibility_proxy:
            return
        self.start_compatible_media_preview(failed_path)

    def fallback_from_unpaintable_media_proxy(self, path: Path, reason: str):
        """Fall back to useful artwork rather than a permanent black window."""
        if self.current_path != path or not self.playing_compatibility_proxy:
            return
        preview_trace(
            "window",
            "compatibility proxy produced no paintable frame",
            path,
            force=True,
            request_id=self.playable_proxy_request_id,
            source_kind=preview_source_kind(self),
            decision="stop Qt playback and show extracted poster",
            backend_message=_clean_process_diagnostic(reason, path, limit=500),
            **video_frame_snapshot(self.video_widget),
            **qmedia_player_snapshot(self.media_player),
        )
        self.cancel_video_artwork_fallback(cancel_worker=True)
        self.playing_compatibility_proxy = False
        self.playback_recovery_source = None
        if self.media_player is not None:
            try:
                self.media_player.stop()
                self.media_player.setSource(QUrl())
            except (AttributeError, RuntimeError):
                pass
        self.start_media_artwork_thumbnail(path)
        self.set_dimmed(bool(self.playback_paused_by_user or self.global_playback_lock_owners))

    def set_media_controls_available(self, available: bool):
        self.media_controls_available = available
        self.scrub_slider.setEnabled(available)
        if hasattr(self, "play_button"):
            self.play_button.setEnabled(available)
        self.mute_button.setEnabled(available)
        self.controls_widget.setVisible(available and not self.cinema_chrome_hidden)

    def stop_media(self):
        self.cancel_video_artwork_fallback(cancel_worker=True)
        self.playable_proxy_request_id += 1
        self.playable_proxy_source = None
        self.playing_compatibility_proxy = False
        self.bound_compatibility_proxy_path = None
        self.awaiting_final_proxy = False
        self._proxy_rebind_generation += 1
        self._proxy_rebind_pending = False
        self._provisional_resume_position_ms = 0
        self.playback_recovery_source = None
        self.scrub_seeker.cancel()
        self.pending_media_seek_ms = None
        self.scrub_was_playing = False
        self.priming_paused_frame = False
        reset_preview_audio_monitor(self)
        if self.media_player is not None:
            try:
                self.media_player.stop()
                self.media_player.setSource(QUrl())
            except Exception:
                pass
        if self.video_widget is not None:
            self.video_widget.reset_player_output(self.media_player)
            self.video_widget.clear_frame(clear_poster=True)
        # QMediaPlayer must release a progressive temporary file before its
        # worker is interrupted and removes that file.
        stop_preview_worker_collection(list(self.playable_proxy_workers), wait_for_exit=False)
        self.playable_proxy_workers.clear()
        self.set_dimmed(False)

    def pause_video_preview(self):
        if self.media_player is None:
            return
        self.playback_paused_by_user = True
        try:
            if self.media_player.playbackState() == QMediaPlayer.PlaybackState.PlayingState:
                self.media_player.pause()
            self.set_dimmed(True)
        except Exception:
            pass

    def suspend_for_large_preview(self, owner) -> None:
        """Temporarily yield transport without rewriting the user's pause state."""
        if owner not in self.global_playback_lock_owners:
            self.global_playback_lock_owners.append(owner)
        self.priming_paused_frame = False
        try:
            if (
                self.media_player is not None
                and self.media_player.playbackState() == QMediaPlayer.PlaybackState.PlayingState
            ):
                self.media_player.pause()
        except (AttributeError, RuntimeError):
            pass
        self.set_dimmed(True)
        self.show_cinema_chrome(schedule_hide=False)
        preview_trace(
            "window",
            "playback yielded to another Preview window",
            self.current_path,
            force=True,
            decision="temporary ownership lock; preserve user pause preference",
            logical_paused=bool(self.playback_paused_by_user),
            lock_count=len(self.global_playback_lock_owners),
        )

    def release_large_preview(self, owner) -> None:
        """Restore this Preview after a newer window relinquishes ownership."""
        self.global_playback_lock_owners = [
            item for item in self.global_playback_lock_owners if item is not owner
        ]
        if self.global_playback_lock_owners:
            return
        if self.media_player is None or self.current_path is None or not is_media_path(self.current_path):
            return
        if self.playback_paused_by_user:
            self.set_dimmed(True)
            return
        try:
            # If a progressive worker is still preparing, its ready callback
            # will start playback. Otherwise resume the already loaded source.
            source = self.media_player.source()
            if source is not None and not source.isEmpty():
                request_video_playback(self)
                self.media_player.play()
                self.set_dimmed(False)
        except (AttributeError, RuntimeError, TypeError):
            pass

    def set_dimmed(self, dimmed: bool):
        self.media_dimmed = bool(dimmed)
        video_is_visible = self.video_widget is not None and self.stack.currentWidget() is self.video_widget
        if hasattr(self, "play_button"):
            self.play_button.setText("▶" if dimmed else "⏸")
            self.play_button.setToolTip("Play" if dimmed else "Pause")
        if self.video_widget is not None:
            self.video_widget.set_paused(dimmed and video_is_visible)
        if hasattr(self, "paused_overlay"):
            try:
                # AspectPixmapLabel paints from its source pixmap rather than
                # QLabel's storage so large artwork cannot affect size hints.
                image = getattr(self.image_label, "_source_pixmap", None)
                image_has_visual = image is not None and not image.isNull()
            except (AttributeError, RuntimeError):
                image_has_visual = False
            visible = (
                dimmed
                and self.isVisible()
                and self.current_path is not None
                and is_media_path(self.current_path)
                and self.stack.currentWidget() is self.image_label
                and image_has_visual
            )
            self.paused_overlay.setVisible(visible)
            if visible:
                self.position_cinema_overlays()
                self.paused_overlay.raise_()
                if self.chrome_overlay_mode:
                    if self.auto_next_label.isVisible():
                        self.auto_next_label.raise_()
                    self.sync_cinema_overlay_window(raise_window=True)
                    self.update_cinema_overlay_mask()
            elif self.chrome_overlay_mode:
                self.update_cinema_overlay_mask()

    def toggle_video_playback(self, trigger: str = "playback control"):
        if self.media_player is None:
            debug_log(
                "response",
                "playback request ignored",
                force=True,
                trigger=trigger,
                reason="no media player",
            )
            return
        try:
            before = self.media_player.playbackState()
            debug_log(
                "input",
                "playback toggle requested",
                force=True,
                trigger=trigger,
                before=str(before),
                full=self.isFullScreen(),
                cinema=bool(self.property("cinema")),
            )
            if self.global_playback_lock_owners:
                # The clicked window is now authoritative. request_video_playback
                # transfers the temporary lock and pauses the previous owner
                # without altering either user's remembered pause preference.
                self.playback_paused_by_user = False
                self.priming_paused_frame = False
                self.apply_mute()
                request_video_playback(self)
                self.media_player.play()
                self.set_dimmed(False)
                self.show_cinema_chrome(schedule_hide=self.isFullScreen())
                outcome = "playing"
            elif not self.playback_paused_by_user:
                self.cancel_auto_next_countdown()
                self.playback_paused_by_user = True
                self.media_player.pause()
                self.set_dimmed(True)
                self.show_cinema_chrome()
                outcome = "paused"
            else:
                self.cancel_auto_next_countdown()
                self.playback_paused_by_user = False
                self.priming_paused_frame = False
                self.apply_mute()
                request_video_playback(self)
                self.media_player.play()
                self.set_dimmed(False)
                self.show_cinema_chrome(schedule_hide=self.isFullScreen())
                outcome = "playing"
            preview_trace(
                "window",
                "user changed playback intent",
                self.current_path,
                force=True,
                request_id=self.playable_proxy_request_id,
                source_kind=preview_source_kind(self),
                decision=outcome,
                trigger=trigger,
                logical_paused=bool(
                    self.playback_paused_by_user or self.global_playback_lock_owners
                ),
            )
            debug_log(
                "response",
                "playback state applied",
                force=True,
                trigger=trigger,
                outcome=outcome,
                dimmed=self.media_dimmed,
            )
        except Exception as exc:
            debug_log(
                "response",
                "playback toggle failed",
                force=True,
                trigger=trigger,
                error=type(exc).__name__,
            )

    def seek_relative_fraction(self, fraction: float):
        if self.media_player is None or self.media_duration_ms <= 0:
            return
        current = (
            self.pending_media_seek_ms
            if self.pending_media_seek_ms is not None
            else self.scrub_seeker.preferred_position(
                preview_player_position_ms(self.media_player)
            )
        )
        target = max(0, min(self.media_duration_ms, int(current + self.media_duration_ms * fraction)))
        self.seek_to_position(target)

    def seek_relative_ms(self, delta_ms: int, continuous: bool = False):
        if self.media_player is None or self.media_duration_ms <= 0:
            return
        current = (
            self.pending_media_seek_ms
            if self.pending_media_seek_ms is not None
            else self.scrub_seeker.preferred_position(
                preview_player_position_ms(self.media_player)
            )
        )
        target = max(0, min(self.media_duration_ms, current + int(delta_ms)))
        if continuous:
            self.suppress_next_end_countdown = True
        self.seek_to_position(target)

    def seek_to_position(self, target: int):
        if self.media_player is None or self.media_duration_ms <= 0:
            return
        target = max(0, min(self.media_duration_ms, int(target)))
        if target < max(0, self.media_duration_ms - self.seek_boundary_margin_ms):
            self.suppress_next_end_countdown = False
        if self.media_source_ready_for_seek(target):
            self.pending_media_seek_ms = None
            self.scrub_seeker.commit(target, reason="preview keyboard seek")
        else:
            self.scrub_seeker.cancel()
            self.pending_media_seek_ms = target
            if not self.playback_paused_by_user:
                try:
                    self.media_player.pause()
                except (AttributeError, RuntimeError):
                    pass
        self.scrub_slider.setValue(target)
        self.update_time_label(target)

    def toggle_full_screen(self):
        debug_log(
            "input",
            "preview fullscreen button activated",
            force=True,
            full=self.isFullScreen(),
            cinema=bool(self.property("cinema")),
            width=self.width(),
            height=self.height(),
        )
        if self.isFullScreen():
            self.exit_cinema_mode()
        else:
            self.enter_cinema_mode()

    def enter_cinema_mode(self):
        if self.exiting_cinema:
            debug_log("response", "cinema entry ignored during exit", force=True)
            return
        if not self.isFullScreen() and not bool(self.property("cinema")):
            self.cinema_session_id += 1
        debug_log(
            "input",
            "cinema mode requested",
            session=self.cinema_session_id,
            full=self.isFullScreen(),
            media_kind=kind_for_path(self.current_path) if self.current_path else "none",
            x=self.x(),
            y=self.y(),
            width=self.width(),
            height=self.height(),
        )
        if not self.isFullScreen() and not self.chrome_overlay_mode:
            self.windowed_geometry_settle_timer.stop()
            self.capture_windowed_geometry_for_cinema()
        self.cinema_restore_geometry = None
        self.exiting_cinema = False
        self.cinema_entry_pending = True
        self.header_opacity.setOpacity(1.0)
        self.controls_opacity.setOpacity(1.0)
        # Use one deterministic Qt fullscreen transition. Mixing Cocoa's native
        # fullscreen animation with a delayed Qt fallback caused maximize/normal/
        # fullscreen bouncing and temporarily dead controls. The green button is
        # promoted into this same code path.
        self.showFullScreen()
        self.fullscreen_btn.setText("Exit Full Screen")
        debug_log(
            "response",
            "cinema transition requested",
            session=self.cinema_session_id,
            native=False,
            width=self.width(),
            height=self.height(),
        )

    def exit_cinema_mode(self, native_transition_started: bool = False):
        if self.exiting_cinema:
            debug_log("large-preview", "exit cinema ignored; already exiting")
            return
        session_id = self.cinema_session_id
        debug_log(
            "input",
            "cinema exit requested",
            session=session_id,
            full=self.isFullScreen(),
            chrome_overlay=self.chrome_overlay_mode,
            width=self.width(),
            height=self.height(),
        )
        self.exiting_cinema = True
        self.cinema_restore_verify_timer.stop()
        self.cinema_restore_verify_attempts = 0
        self.cinema_restore_stable_checks = 0
        self.cinema_restore_started_at = time.monotonic()
        self.cinema_restore_last_state_change = self.cinema_restore_started_at
        self.cinema_restore_verify_deadline = self.cinema_restore_started_at + 8.0
        self.cinema_restore_fallback_issued = False
        self.cinema_restore_geometry_applied = False
        self.cinema_restore_context_prepared = False
        if self.windowed_geometry_before_cinema is not None:
            self.cinema_restore_geometry = QRect(self.windowed_geometry_before_cinema)
        if native_transition_started or not self.isFullScreen():
            self.finish_cinema_ui_exit()
        else:
            self.cinema_restore_fallback_issued = True
            self.showNormal()
        self.cinema_restore_verify_timer.start(120)

    def finish_cinema_ui_exit(self):
        self.cinema_timer.stop()
        self.cancel_auto_next_countdown()
        self.hide_cinema_overlay_window()
        self.fullscreen_btn.setText("Full Screen")
        if bool(self.property("cinema")) or self.chrome_overlay_mode:
            self.set_cinema_style(False)
        self.show_cinema_chrome()

    def verify_cinema_restore_geometry(self):
        if not self.exiting_cinema:
            return
        target_geometry = self.windowed_geometry_before_cinema or self.cinema_restore_geometry
        if target_geometry is None:
            self.finish_cinema_ui_exit()
            self.exiting_cinema = False
            return
        placement = self.windowed_placement_before_cinema or self.last_windowed_placement
        target = restore_rect_for_window_placement(self, placement, QRect(target_geometry))
        actual = QRect(self.geometry())
        state = self.windowState()
        wrong_state = bool(state & (Qt.WindowFullScreen | Qt.WindowMaximized))
        wrong_geometry = any(
            (
                abs(actual.x() - target.x()) > 3,
                abs(actual.y() - target.y()) > 3,
                abs(actual.width() - target.width()) > 3,
                abs(actual.height() - target.height()) > 3,
            )
        )
        now = time.monotonic()
        self.cinema_restore_verify_attempts += 1
        if wrong_state:
            self.cinema_restore_stable_checks = 0
            # Native Cocoa transitions are asynchronous. Observe first; only if
            # the transition genuinely stalls do one Qt fallback request.
            if (
                not self.cinema_restore_fallback_issued
                and now - self.cinema_restore_started_at >= 3.0
            ):
                self.cinema_restore_fallback_issued = True
                debug_log(
                    "response",
                    "cinema exit native transition stalled; applying one fallback",
                    force=True,
                    full=self.isFullScreen(),
                    maximized=bool(state & Qt.WindowMaximized),
                )
                self.showNormal()
            if now < self.cinema_restore_verify_deadline:
                self.cinema_restore_verify_timer.start(260)
                return
        else:
            self.finish_cinema_ui_exit()
            # Give Cocoa a quiet interval after leaving its Space before touching
            # geometry. This prevents our correction from racing its own restore.
            if now - self.cinema_restore_last_state_change < 0.55:
                self.cinema_restore_verify_timer.start(180)
                return
            if not self.cinema_restore_context_prepared:
                self.cinema_restore_context_prepared = True
                delay = prepare_macos_window_restore_context(self, self.owner_window)
                if delay:
                    self.cinema_restore_verify_timer.start(delay)
                    return
            if wrong_geometry and not self.cinema_restore_geometry_applied:
                self.cinema_restore_geometry_applied = True
                self.setGeometry(target)
                self.last_windowed_geometry = QRect(target)
                self.last_windowed_placement = capture_window_placement(self, target)
                self.cinema_restore_verify_timer.start(220)
                return
            actual = QRect(self.geometry())
            wrong_geometry = any(
                (
                    abs(actual.x() - target.x()) > 3,
                    abs(actual.y() - target.y()) > 3,
                    abs(actual.width() - target.width()) > 3,
                    abs(actual.height() - target.height()) > 3,
                )
            )
        if not wrong_state and not wrong_geometry:
            self.cinema_restore_stable_checks += 1
            if self.cinema_restore_stable_checks < 3:
                self.cinema_restore_verify_timer.start(180)
                return
            debug_log(
                "response",
                "cinema exit finished",
                force=True,
                session=self.cinema_session_id,
                full=False,
                maximized=False,
                cinema=bool(self.property("cinema")),
                x=actual.x(),
                y=actual.y(),
                width=actual.width(),
                height=actual.height(),
            )
            self.exiting_cinema = False
            self.windowed_geometry_before_cinema = None
            self.windowed_placement_before_cinema = None
            self.cinema_restore_geometry = None
            self.cinema_restore_verify_attempts = 0
            self.cinema_restore_stable_checks = 0
            self.cinema_restore_verify_deadline = 0.0
            self.cinema_restore_started_at = 0.0
            self.cinema_restore_last_state_change = 0.0
            self.cinema_restore_fallback_issued = False
            self.cinema_restore_geometry_applied = False
            self.cinema_restore_context_prepared = False
            return
        self.cinema_restore_stable_checks = 0
        if now >= self.cinema_restore_verify_deadline:
            debug_log(
                "response",
                "cinema exit settlement failed",
                force=True,
                attempts=self.cinema_restore_verify_attempts,
                full=self.isFullScreen(),
                maximized=bool(state & Qt.WindowMaximized),
                actual_width=actual.width(),
                actual_height=actual.height(),
                expected_width=target.width(),
                expected_height=target.height(),
            )
            self.exiting_cinema = False
            self.windowed_geometry_before_cinema = None
            self.windowed_placement_before_cinema = None
            self.cinema_restore_geometry = None
            self.cinema_restore_started_at = 0.0
            self.cinema_restore_last_state_change = 0.0
            self.cinema_restore_context_prepared = False
            return
        if self.cinema_restore_verify_attempts == 1 or self.cinema_restore_verify_attempts % 8 == 0:
            debug_log(
                "response",
                "cinema exit settling",
                attempt=self.cinema_restore_verify_attempts,
                full=self.isFullScreen(),
                maximized=bool(state & Qt.WindowMaximized),
                actual_width=actual.width(),
                actual_height=actual.height(),
                expected_width=target.width(),
                expected_height=target.height(),
            )
        self.cinema_restore_verify_timer.start(260)

    def handle_escape_shortcut(self):
        debug_log(
            "large-preview",
            "escape shortcut",
            force=True,
            full=self.isFullScreen(),
            chrome_overlay=self.chrome_overlay_mode,
            cinema=bool(self.property("cinema")),
            exiting=self.exiting_cinema,
        )
        if self.exiting_cinema:
            self.cinema_restore_verify_timer.start(0)
            return
        if self.isFullScreen() or self.chrome_overlay_mode or bool(self.property("cinema")):
            self.exit_cinema_mode()
        elif self.isActiveWindow():
            self.close()

    def handle_space_shortcut(self):
        # Cinema/fullscreen: Space toggles play/pause. Normal preview window:
        # Space closes the preview, matching the native Quick Look rhythm.
        if self.isFullScreen() and self.current_path and is_media_path(self.current_path):
            self.toggle_video_playback("Space shortcut")
        elif not self.isFullScreen():
            debug_log("input", "Space requested preview close", force=True, full=False)
            self.close()

    def set_cinema_style(self, enabled: bool):
        if enabled:
            self.enter_cinema_overlay_mode()
        else:
            self.leave_cinema_overlay_mode()
        self.setProperty("cinema", enabled)
        self.style().unpolish(self)
        self.style().polish(self)
        self.preview_layout.setContentsMargins(0 if enabled else 14, 0 if enabled else 14, 0 if enabled else 14, 0 if enabled else 14)
        self.preview_layout.setSpacing(0 if enabled else 10)
        inset = 0
        if hasattr(self, "header_layout"):
            self.header_layout.setContentsMargins(inset, 8 if enabled else 0, inset, 8 if enabled else 0)
        if hasattr(self, "controls_layout"):
            self.controls_layout.setContentsMargins(inset, 8 if enabled else 0, inset, 8 if enabled else 0)

        for widget in (
            self.header_widget,
            self.controls_widget,
            self.stack,
            self.placeholder,
            self.image_label,
            self.text_view,
        ):
            widget.setProperty("cinema", enabled)
            widget.style().unpolish(widget)
            widget.style().polish(widget)
        if self.video_widget is not None:
            self.video_widget.setProperty("cinema", enabled)
            self.video_widget.style().unpolish(self.video_widget)
            self.video_widget.style().polish(self.video_widget)
        for widget in (
            self.title_label,
            self.meta_label,
            self.time_label,
            self.play_button,
            self.fullscreen_btn,
            self.close_btn,
            self.mute_button,
            self.scrub_slider,
        ):
            widget.setProperty("cinema", enabled)
            widget.style().unpolish(widget)
            widget.style().polish(widget)

    def start_continuous_seek(self):
        if self.seek_hold_direction == 0:
            return
        self.cancel_auto_next_countdown()
        self.suppress_next_end_countdown = True
        self.seek_hold_active = True
        self.seek_hold_last_at = time.monotonic()
        self.seek_hold_restore_pause = not self.media_is_playing()
        self.show_cinema_chrome(schedule_hide=False)
        if self.seek_hold_restore_pause and self.media_player is not None:
            try:
                self.temporary_playback_override = True
                request_video_playback(self)
                self.media_player.play()
                self.set_dimmed(False)
            except Exception:
                pass
        self.continuous_seek_tick()
        self.seek_hold_timer.start()

    def continuous_seek_tick(self):
        if self.seek_hold_direction == 0:
            return
        if self.media_player is None or self.media_duration_ms <= 0:
            return
        if self.seek_hold_direction > 0 and self.at_media_end():
            self.seek_to_position(self.media_duration_ms)
            return
        if self.seek_hold_direction < 0 and self.at_media_start():
            self.seek_to_position(0)
            return

        now = time.monotonic()
        elapsed = max(0.01, min(0.08, now - (self.seek_hold_last_at or now)))
        self.seek_hold_last_at = now
        step_ms = int(self.media_duration_ms * 0.05 * elapsed)
        step_ms = max(80, min(2500, step_ms))
        self.seek_relative_ms(step_ms * self.seek_hold_direction, continuous=True)

    def stop_seek_hold(self):
        was_active = self.seek_hold_active
        restore_pause = self.seek_hold_restore_pause
        self.seek_hold_delay.stop()
        self.seek_hold_timer.stop()
        self.seek_hold_direction = 0
        self.seek_hold_active = False
        self.seek_hold_last_at = 0.0
        self.seek_hold_restore_pause = False
        if not was_active:
            return
        if restore_pause and self.media_player is not None:
            try:
                self.temporary_playback_override = False
                self.media_player.pause()
                self.set_dimmed(True)
            except Exception:
                pass
            self.show_cinema_chrome()
        elif self.isFullScreen():
            self.temporary_playback_override = False
            self.show_cinema_chrome(schedule_hide=self.media_is_playing())

    def apply_mute(self):
        sync_output = getattr(self, "_sync_default_audio_output", None)
        if callable(sync_output):
            sync_output()
        if self.audio_output is not None:
            self.audio_output.setMuted(self.preview_muted)
            self.audio_output.setVolume(0.0 if self.preview_muted else 0.85)
        self.mute_button.setText("Muted" if self.preview_muted else "Sound")

    def toggle_mute(self):
        debug_log(
            "input",
            "preview sound button activated",
            force=True,
            muted_before=self.preview_muted,
        )
        self.preview_muted = not self.preview_muted
        self.settings.setValue("preview/muted", self.preview_muted)
        self.apply_mute()
        self.sync_other_preview_mutes()
        debug_log(
            "response",
            "preview sound state changed",
            force=True,
            muted=self.preview_muted,
        )

    def set_preview_muted(self, muted: bool):
        self.preview_muted = muted
        self.apply_mute()

    def sync_other_preview_mutes(self):
        for owner in list(VIDEO_PLAYBACK_OWNERS):
            if owner is self:
                continue
            setter = getattr(owner, "set_preview_muted", None)
            if callable(setter):
                setter(self.preview_muted)

    def on_duration_changed(self, duration: int):
        backend_duration = max(0, int(duration))
        previous_duration = self.media_duration_ms
        self.media_duration_ms = max(
            self.media_duration_ms,
            backend_duration,
            self.metadata_duration_ms,
        )
        self.scrub_slider.setRange(0, self.media_duration_ms)
        self.update_time_label(self.scrub_slider.value())
        if self.media_duration_ms != previous_duration:
            preview_trace(
                "window",
                "preview timeline duration updated",
                self.current_path,
                request_id=self.playable_proxy_request_id,
                source_kind=preview_source_kind(self),
                backend_duration_ms=backend_duration,
                metadata_duration_ms=self.metadata_duration_ms,
                effective_duration_ms=self.media_duration_ms,
                provisional_proxy=bool(self.awaiting_final_proxy),
            )
        self.apply_pending_media_seek()

    def on_position_changed(self, position: int):
        if self.scrubbing_video or self.pending_media_seek_ms is not None:
            return
        reason = self.scrub_seeker.committed_reason
        visible_position, event, target = self.scrub_seeker.filter_backend_position(position)
        if self._proxy_rebind_pending and target is None:
            return
        if self.playing_compatibility_proxy and self.awaiting_final_proxy:
            if visible_position <= 0 and self._provisional_resume_position_ms > 0:
                visible_position = self._provisional_resume_position_ms
            elif visible_position > 0:
                self._provisional_resume_position_ms = visible_position
        self.scrub_slider.setValue(visible_position)
        self.update_time_label(visible_position)
        if event:
            preview_trace(
                "window",
                f"seek backend {event}",
                self.current_path,
                force=True,
                request_id=self.playable_proxy_request_id,
                source_kind=preview_source_kind(self),
                requested_position_ms=target,
                backend_position_ms=max(0, int(position)),
                visible_position_ms=visible_position,
                available_duration_ms=preview_player_duration_ms(
                    self.media_player,
                    self.media_duration_ms,
                ),
                seek_reason=reason,
                rebind_pending=bool(self._proxy_rebind_pending),
            )

    def on_playback_state_changed(self, state):
        state_name = qt_enum_name(state)
        transition_key = (
            preview_item_id(self.current_path),
            self.playable_proxy_request_id,
            preview_source_kind(self),
            state_name,
        )
        if self._debug_last_playback_state != transition_key:
            self._debug_last_playback_state = transition_key
            preview_trace(
                "window",
                "Qt playback state changed",
                self.current_path,
                request_id=self.playable_proxy_request_id,
                source_kind=preview_source_kind(self),
                state=state_name,
                playback_state=state_name,
                logical_paused=bool(
                    self.playback_paused_by_user or self.global_playback_lock_owners
                ),
                **qmedia_player_snapshot(self.media_player),
            )
        if self.temporary_playback_override:
            self.set_dimmed(False)
        elif self.playback_paused_by_user or self.global_playback_lock_owners:
            self.set_dimmed(True)
            self.show_cinema_chrome()
        elif self.scrubbing_video and self.scrub_was_playing:
            # setPosition may transiently advertise PausedState. Keep the video
            # and chrome in their playing presentation throughout a drag.
            return
        else:
            # Loading and seek transitions are not user pause requests.
            self.set_dimmed(False)
            if QMediaPlayer and state == QMediaPlayer.PlaybackState.PlayingState:
                self.schedule_cinema_hide()

    def on_media_status_changed(self, status):
        status_name = qt_enum_name(status)
        transition_key = (
            preview_item_id(self.current_path),
            self.playable_proxy_request_id,
            preview_source_kind(self),
            status_name,
        )
        if self._debug_last_media_status != transition_key:
            self._debug_last_media_status = transition_key
            preview_trace(
                "window",
                "Qt media status changed",
                self.current_path,
                request_id=self.playable_proxy_request_id,
                source_kind=preview_source_kind(self),
                status=status_name,
                media_status=status_name,
                logical_paused=bool(
                    self.playback_paused_by_user or self.global_playback_lock_owners
                ),
                **qmedia_player_snapshot(self.media_player),
            )
        if (
            QMediaPlayer
            and status == QMediaPlayer.MediaStatus.EndOfMedia
            and self.playing_compatibility_proxy
            and self.awaiting_final_proxy
        ):
            self.cancel_auto_next_countdown()
            available_duration = preview_player_duration_ms(
                self.media_player,
                self.media_duration_ms,
            )
            edge_position = max(
                self._provisional_resume_position_ms,
                max(0, int(self.scrub_slider.value())),
                preview_player_position_ms(self.media_player),
            )
            if available_duration > 0:
                edge_position = min(edge_position, available_duration)
            self._provisional_resume_position_ms = edge_position
            if self.pending_media_seek_ms is None:
                self.scrub_slider.setValue(edge_position)
                self.update_time_label(edge_position)
            preview_trace(
                "window",
                "provisional proxy reached buffered edge",
                self.current_path,
                force=True,
                request_id=self.playable_proxy_request_id,
                source_kind=preview_source_kind(self),
                decision="hold current position until proxy buffer grows; do not advance or reset",
                backend_position_ms=preview_player_position_ms(self.media_player),
                retained_position_ms=edge_position,
                available_duration_ms=available_duration,
            )
            return
        if (
            QMediaPlayer
            and status == QMediaPlayer.MediaStatus.EndOfMedia
            and self.isFullScreen()
            and self.current_path
            and is_video_path(self.current_path)
        ):
            if self.suppress_next_end_countdown:
                self.cancel_auto_next_countdown()
                return
            self.start_auto_next_countdown()

    def on_video_capabilities_changed(self):
        ensure_active_preview_audio_track(self, "window")
        snapshot = qmedia_player_snapshot(self.media_player)
        signature = (
            preview_item_id(self.current_path),
            self.playable_proxy_request_id,
            preview_source_kind(self),
            snapshot.get("has_video"),
            snapshot.get("has_audio"),
            snapshot.get("player_seekable"),
            snapshot.get("duration_ms"),
        )
        if signature == self._debug_last_capability_signature:
            return
        self._debug_last_capability_signature = signature
        preview_trace(
            "window",
            "Qt media capabilities changed",
            self.current_path,
            request_id=self.playable_proxy_request_id,
            source_kind=preview_source_kind(self),
            logical_paused=bool(self.playback_paused_by_user),
            **snapshot,
        )

    def on_scrub_pressed(self):
        self.scrub_seeker.cancel()
        self.pending_media_seek_ms = None
        self.scrubbing_video = True
        self.scrub_was_playing = False
        if self.media_player is not None and QMediaPlayer is not None:
            try:
                self.scrub_was_playing = (
                    self.media_player.playbackState()
                    == QMediaPlayer.PlaybackState.PlayingState
                )
            except (AttributeError, RuntimeError):
                pass
        self.cancel_auto_next_countdown()

    def on_scrub_released(self):
        seek_position = self.scrub_slider.value()
        try:
            available_duration = preview_player_duration_ms(
                self.media_player,
                self.media_duration_ms,
            )
            seek_applied = self.media_source_ready_for_seek(seek_position)
            if seek_applied:
                self.scrub_seeker.commit(seek_position, reason="user slider seek")
                self.pending_media_seek_ms = None
                if self.awaiting_final_proxy:
                    self._provisional_resume_position_ms = max(0, int(seek_position))
            else:
                self.scrub_seeker.cancel()
                self.pending_media_seek_ms = max(0, int(seek_position))
                if self.scrub_was_playing and self.media_player is not None:
                    self.media_player.pause()
            self.update_time_label(seek_position)
            preview_trace(
                "window",
                "user seek committed" if seek_applied else "user seek deferred",
                self.current_path,
                force=True,
                request_id=self.playable_proxy_request_id,
                source_kind=preview_source_kind(self),
                requested_position_ms=int(seek_position),
                available_duration_ms=available_duration,
                actual_position_ms=preview_player_position_ms(self.media_player),
                decision=(
                    "send one authoritative decoder seek"
                    if seek_applied
                    else "keep requested thumb position until progressive source can honor it"
                ),
                logical_paused=bool(self.playback_paused_by_user),
            )
            if seek_applied and self.scrub_was_playing and self.media_player is not None and QMediaPlayer is not None:
                if (
                    self.media_player.playbackState()
                    != QMediaPlayer.PlaybackState.PlayingState
                ):
                    self.media_player.play()
        except (AttributeError, RuntimeError):
            pass
        finally:
            self.scrubbing_video = False
            self.scrub_was_playing = False

    def on_scrub_moved(self, position: int):
        self.update_time_label(position)
        if self.scrubbing_video:
            return
        if self.media_source_ready_for_seek(position):
            self.pending_media_seek_ms = None
            self.scrub_seeker.commit(position, reason="slider keyboard seek")
            if self.awaiting_final_proxy:
                self._provisional_resume_position_ms = max(0, int(position))
        else:
            self.scrub_seeker.cancel()
            self.pending_media_seek_ms = max(0, int(position))

    def update_time_label(self, position: int):
        if hasattr(self, "time_label"):
            self.time_label.setText(f"{format_ms(position)} / {format_ms(self.media_duration_ms)}")

    def refresh_from_owner(self):
        if self.current_path_provider:
            path = self.current_path_provider()
            if path and path.exists():
                self.set_path(path)
                return
        self.close()

    def keyPressEvent(self, event):
        key = event.key()
        modifiers = event.modifiers()
        command = bool(modifiers & (Qt.ControlModifier | Qt.MetaModifier))
        if key == Qt.Key_Escape:
            debug_log(
                "input",
                "Escape pressed in preview",
                force=True,
                full=self.isFullScreen(),
                cinema=bool(self.property("cinema")),
                width=self.width(),
                height=self.height(),
            )
            if self.isFullScreen():
                self.exit_cinema_mode()
            else:
                debug_log("response", "windowed preview closing from Escape", force=True)
                self.close()
            event.accept()
            return
        if key == Qt.Key_F and not modifiers:
            self.toggle_full_screen()
            event.accept()
            return
        if key == Qt.Key_Space:
            if time.monotonic() - self.opened_at < 0.28:
                event.accept()
                return
            if self.isFullScreen():
                self.toggle_video_playback("Space key")
            else:
                debug_log(
                    "input",
                    "Space pressed in windowed preview",
                    force=True,
                    response="close preview",
                )
                self.close()
            event.accept()
            return
        if key in (Qt.Key_Return, Qt.Key_Enter):
            self.toggle_video_playback("Return key")
            event.accept()
            return
        if key in (Qt.Key_Left, Qt.Key_Right):
            if event.isAutoRepeat():
                event.accept()
                return
            self.seek_hold_direction = -1 if key == Qt.Key_Left else 1
            self.seek_hold_active = False
            self.seek_hold_delay.start(360)
            event.accept()
            return
        if key in (Qt.Key_Up, Qt.Key_Down):
            if event.isAutoRepeat():
                event.accept()
                return
            direction = -1 if key == Qt.Key_Up else 1
            before = self.effective_path()
            debug_log(
                "input",
                "preview row navigation requested",
                force=True,
                direction="previous" if direction < 0 else "next",
                full=self.isFullScreen(),
                width=self.width(),
                height=self.height(),
            )
            result = self.step_callback(direction)
            # Owner callbacks often synchronize a backing table/tree. They must
            # not leave keyboard focus in that other window after navigation.
            QTimer.singleShot(0, self.ensure_preview_input_focus)
            debug_log(
                "response",
                "preview row navigation applied",
                force=True,
                direction="previous" if direction < 0 else "next",
                changed=self.effective_path() != before,
                callback_result=result,
                full=self.isFullScreen(),
                width=self.width(),
                height=self.height(),
            )
            event.accept()
            return
        if key in (Qt.Key_Delete, Qt.Key_Backspace) and command:
            self.delete_callback()
            QTimer.singleShot(80, self.refresh_from_owner)
            event.accept()
            return
        super().keyPressEvent(event)

    def keyReleaseEvent(self, event):
        key = event.key()
        if key in (Qt.Key_Left, Qt.Key_Right):
            if event.isAutoRepeat():
                event.accept()
                return
            direction = self.seek_hold_direction
            was_continuous = self.seek_hold_active
            self.stop_seek_hold()
            if direction and was_continuous:
                if direction > 0 and self.at_media_end():
                    self.seek_to_position(self.media_duration_ms)
                elif direction < 0 and self.at_media_start():
                    self.seek_to_position(0)
            elif direction:
                if direction > 0 and self.jump_to_next_video_now():
                    pass
                elif direction > 0 and self.at_media_end():
                    if not self.step_video_from_boundary(1):
                        self.show_cinema_edge_message("End of list")
                elif direction < 0 and self.at_media_start():
                    if not self.step_video_from_boundary(-1):
                        self.show_cinema_edge_message("Start of list")
                else:
                    self.seek_relative_fraction(0.1 * direction)
            event.accept()
            return
        super().keyReleaseEvent(event)

    def closeEvent(self, event):
        debug_window_close_context(self, "preview")
        # Never destroy the Qt content tree while Cocoa is still moving a
        # fullscreen window between Spaces. Doing so is what produces the
        # orphan white shell seen after closing fullscreen Preview/Debug windows.
        if defer_close_until_windowed(self, event, "preview"):
            return
        save_window_geometry(self, "preview")
        debug_log(
            "input",
            "preview close requested",
            force=True,
            full=self.isFullScreen(),
            maximized=bool(self.windowState() & Qt.WindowMaximized),
            cinema=bool(self.property("cinema")),
            x=self.x(),
            y=self.y(),
            width=self.width(),
            height=self.height(),
        )
        app = QApplication.instance()
        if app is not None:
            try:
                app.removeEventFilter(self)
            except Exception:
                pass
        unregister_video_owner(self)
        if hasattr(self, "video_click_timer"):
            self.video_click_timer.stop()
        self.cinema_restore_verify_timer.stop()
        self.exiting_cinema = False
        self.cinema_entry_pending = False
        self.windowed_geometry_before_cinema = None
        self.windowed_placement_before_cinema = None
        self.cinema_restore_geometry = None
        self.cinema_timer.stop()
        self.cancel_auto_next_countdown()
        self.stop_seek_hold()
        # Stop the authoritative transport before unlocking any embedded
        # surface; there must never be an interval with both audio routes live.
        self.stop_media()
        for owner in list(VIDEO_PLAYBACK_OWNERS):
            release = getattr(owner, "release_large_preview", None)
            if callable(release):
                release(self)
        self.release_embedded_preview()
        self.stop_preview_workers()
        self.current_path = None
        self.playback_paused_by_user = False
        self.temporary_playback_override = False
        if self.cinema_overlay_window is not None:
            self.cinema_overlay_window.hide()
            self.cinema_overlay_window.close()
        super().closeEvent(event)
        debug_log("response", "preview window closed", force=True)

    def hideEvent(self, event):
        self.hide_cinema_overlay_window()
        super().hideEvent(event)

    def showEvent(self, event):
        self.opened_at = time.monotonic()
        register_video_owner(self)
        app = QApplication.instance()
        if app is not None:
            try:
                app.installEventFilter(self)
            except Exception:
                pass
        if not self.isFullScreen():
            self.hide_cinema_overlay_window()
        super().showEvent(event)
        if self.current_path is not None:
            try:
                meta = self.meta_provider(self.current_path) if self.meta_provider else None
            except Exception:
                meta = None
            self.sync_embedded_preview(self.current_path, meta)
        temporarily_attach_window_to_owner_space(self, self.owner_window)
        schedule_macos_native_fullscreen_button(self)
        self.remember_current_windowed_geometry()
        if (
            self.opening_windowed_geometry is None
            and self.last_windowed_geometry is not None
        ):
            self.opening_windowed_geometry = QRect(self.last_windowed_geometry)
            self.opening_windowed_placement = self.last_windowed_placement or capture_window_placement(
                self, self.opening_windowed_geometry
            )
        self.schedule_windowed_geometry_remember()
        QTimer.singleShot(0, self.ensure_preview_input_focus)
        QTimer.singleShot(90, self.ensure_preview_input_focus)

    def ensure_preview_input_focus(self):
        """Keep Quick Look keyboard ownership after opening or changing rows."""
        try:
            if not self.isVisible():
                return
            self.raise_()
            self.activateWindow()
            self.setFocus(Qt.ActiveWindowFocusReason)
        except (AttributeError, RuntimeError):
            pass


# ---------------------------------------------------------------------------
# Shared scanner dialog controls


class ScannerDialogBase(QDialog):
    """Common controls and worker lifetime for duplicate and bad-file scans.

    Subclasses build the widgets and own their result models. They provide
    start_scan() and on_background_trash_finished(); this base keeps shutdown,
    trash workers, preview controls, and column sizing consistent.
    """

    def request_details_column_width(self, text: str):
        if not text:
            return
        # Damage explanations live in tooltips too; do not let one long FFmpeg
        # reason stretch the entire scanner window thousands of pixels wide.
        width = min(900, self.tree.fontMetrics().averageCharWidth() * len(text) + 36)
        if width <= max(self.pending_details_column_width, self.tree.columnWidth(self.DETAILS_COLUMN)):
            return
        self.pending_details_column_width = width
        if not self.details_column_timer.isActive():
            self.details_column_timer.start(80)


    def apply_details_column_width(self):
        width = self.pending_details_column_width
        self.pending_details_column_width = 0
        if width > self.tree.columnWidth(self.DETAILS_COLUMN):
            self.tree.setColumnWidth(self.DETAILS_COLUMN, width)


    def handle_scan_button(self):
        if self.worker and self.worker.isRunning():
            self.stop_scan()
        else:
            self.start_scan()


    def stop_scan(self):
        if not self.worker or not self.worker.isRunning():
            return
        self.progress_label.setText("Terminating scan")
        self.scan_btn.setEnabled(False)
        self.worker.request_cancel()
        self.worker.requestInterruption()
        QTimer.singleShot(900, self.force_stop_scan)


    def force_stop_scan(self):
        worker = self.worker
        if not worker or not worker.isRunning():
            return
        worker.request_cancel()
        worker.requestInterruption()
        self.progress_label.setText("Waiting for active media checks to stop")
        QTimer.singleShot(250, self.force_stop_scan)


    def retire_worker(self, worker: Optional[QThread]):
        if worker is None:
            return
        if worker is self.worker:
            self.worker = None
        if worker not in self.retired_workers:
            self.retired_workers.append(worker)
        QTimer.singleShot(0, lambda w=worker: self.cleanup_retired_worker(w))


    def cleanup_retired_worker(self, worker: QThread):
        try:
            if worker.isRunning():
                QTimer.singleShot(150, lambda w=worker: self.cleanup_retired_worker(w))
                return
            worker.wait(10)
        except RuntimeError:
            return
        if worker in self.retired_workers:
            self.retired_workers.remove(worker)
        try:
            worker.deleteLater()
        except RuntimeError:
            pass
        self.maybe_close_after_scan_stops()


    def scan_thread_running(self) -> bool:
        if self.worker and self.worker.isRunning():
            return True
        for worker in list(self.retired_workers):
            try:
                if worker.isRunning():
                    return True
            except RuntimeError:
                continue
        return False


    def trash_thread_running(self) -> bool:
        for worker in list(self.trash_workers):
            try:
                if worker.isRunning():
                    return True
            except RuntimeError:
                continue
        return False


    def stop_background_trash_moves(self):
        for worker in list(self.trash_workers):
            try:
                if worker.isRunning():
                    worker.requestInterruption()
            except RuntimeError:
                continue


    def maybe_close_after_scan_stops(self):
        if (
            self.close_after_scan_stops
            and not self.scan_thread_running()
            and not self.trash_thread_running()
        ):
            self.close_after_scan_stops = False
            QTimer.singleShot(0, self.close)


    def toggle_active_preview_playback(self):
        if self.quicklook_dialog and self.quicklook_dialog.isVisible():
            self.quicklook_dialog.toggle_video_playback()
        else:
            self.preview_panel.toggle_media_playback()


    def update_undo_button(self):
        if not hasattr(self, "undo_btn"):
            return
        self.undo_btn.setEnabled(bool(self.undo_stack))
        self.undo_btn.setToolTip("Undo last scanner delete (Command-Z)" if self.undo_stack else "Nothing to undo")


    def start_background_trash_move(self, paths: List[Path]):
        worker = TrashMoveWorker(paths)
        self.trash_workers.append(worker)
        worker.progress.connect(lambda done, total: self.progress_label.setText(
            f"Moving to Trash {human_count(done)}/{human_count(total)}"
        ))
        worker.results_ready.connect(
            lambda moves, failures, worker=worker: self.on_background_trash_finished(worker, moves, failures)
        )
        worker.finished.connect(
            lambda worker=worker, owners=self.trash_workers: retire_thread_worker(worker, owners)
        )
        worker.finished.connect(lambda: QTimer.singleShot(0, self.maybe_close_after_scan_stops))
        self.progress_label.setText(f"Moving {human_count(len(paths))} file(s) to Trash in background")
        worker.start()


# ---------------------------------------------------------------------------
# Duplicate results dialog


class DuplicateDialog(ScannerDialogBase):
    ROLE_KIND = Qt.UserRole
    ROLE_GROUP = Qt.UserRole + 1
    ROLE_PATH = Qt.UserRole + 2
    ROLE_SUBGROUP = Qt.UserRole + 3
    DAMAGE_COLUMN = 3
    SIZE_COLUMN = 4
    DURATION_COLUMN = 5
    SAMPLE_RATE_COLUMN = 6
    RESOLUTION_COLUMN = 7
    LOCATION_COLUMN = 8
    DETAILS_COLUMN = 9

    def __init__(self, folder: Path, parent=None, scan_files: Optional[List[Path]] = None):
        # Scanner windows are peers, not macOS transient children. Keeping a
        # native parent makes AppKit move/reorder the whole family across Spaces.
        super().__init__(None)
        self.owner_window = top_level_window_for(parent)
        self.setWindowFlag(Qt.Window, True)
        self.setWindowModality(Qt.NonModal)
        self.setModal(False)
        try:
            self.setWindowFlag(Qt.WindowType.WindowFullscreenButtonHint, True)
        except Exception:
            pass
        self.setWindowTitle("Duplicate Scan")
        self.resize(1220, 760)
        self.folder = folder
        self.scan_files = list(scan_files) if scan_files is not None else None
        self.worker: Optional[DuplicateWorker] = None
        self.retired_workers: List[DuplicateWorker] = []
        self.close_after_scan_stops = False
        self.group_items: Dict[int, List[DupItem]] = {}
        self.group_header_items: Dict[int, QTreeWidgetItem] = {}
        self.group_fingerprints: Dict[int, Tuple] = {}
        self.user_collapsed_group_ids: set[int] = set()
        self.user_collapsed_subgroups: set[Tuple[int, str]] = set()
        self.all_dup_items: List[DupItem] = []
        self.dup_items_by_path: Dict[str, List[DupItem]] = defaultdict(list)
        self.live_metadata_cache: Dict[Path, MediaMeta] = {}
        self.live_health_cache: Dict[str, Tuple[str, str, str]] = {}
        self.cleaned_group_items: Dict[int, List[DupItem]] = {}
        self.deleted_dup_items_by_path: Dict[Path, List[DupItem]] = defaultdict(list)
        self.suppressed_paths: set[Path] = set()
        self.undo_stack: List[TrashAction] = []
        self.redo_stack: List[TrashAction] = []
        self.trash_workers: List[TrashMoveWorker] = []
        self.active_review_folder: Optional[Path] = None
        self.active_review_moves: List[ReviewMove] = []
        self.review_watcher: Optional[FinderWindowWatcher] = None
        self.preview_navigation_active = False
        self.current_active_file_path: Optional[Path] = None
        self.previous_active_file_path: Optional[Path] = None
        self.renaming_item: Optional[QTreeWidgetItem] = None
        self.renaming_path: Optional[Path] = None
        self.rename_suppress = False
        self.filtering_selection = False
        self.quicklook_dialog: Optional["LargePreviewDialog"] = None
        self.last_preview_toggle_at = 0.0
        self.pending_duplicate_preview_path: Optional[Path] = None
        self.duplicate_preview_timer = QTimer(self)
        self.duplicate_preview_timer.setSingleShot(True)
        self.duplicate_preview_timer.timeout.connect(self.apply_pending_duplicate_preview)
        self.pending_partial_items: Optional[List[DupItem]] = None
        self.pending_partial_signature: Optional[Tuple[int, int, int]] = None
        self.rendered_partial_signature: Optional[Tuple[int, int, int]] = None
        self.last_partial_apply_at = 0.0
        self.scan_progress_text = "Ready"
        self.partial_results_timer = QTimer(self)
        self.partial_results_timer.setSingleShot(True)
        self.partial_results_timer.timeout.connect(self.apply_pending_partial_results)
        self.pending_metadata_group_ids: set[int] = set()
        self.metadata_rows_timer = QTimer(self)
        self.metadata_rows_timer.setSingleShot(True)
        self.metadata_rows_timer.timeout.connect(self.flush_duplicate_metadata_rows)
        self.pending_details_column_width = 0
        self.details_column_timer = QTimer(self)
        self.details_column_timer.setSingleShot(True)
        self.details_column_timer.timeout.connect(self.apply_details_column_width)
        self.duplicate_tree_loader_timer = QTimer(self)
        self.duplicate_tree_loader_timer.setSingleShot(True)
        self.duplicate_tree_loader_timer.timeout.connect(self.load_next_duplicate_tree_chunk)
        self._duplicate_tree_loading = False
        self._duplicate_tree_pending_group_ids = deque()
        self._duplicate_tree_latest_items: Optional[List[DupItem]] = None

        layout = QVBoxLayout(self)
        layout.setContentsMargins(14, 14, 14, 14)
        layout.setSpacing(10)

        header = QHBoxLayout()
        layout.addLayout(header)

        title_box = QVBoxLayout()
        title_box.setSpacing(1)
        header.addLayout(title_box, stretch=1)

        title = QLabel("Duplicate Scan")
        title.setObjectName("SectionTitle")
        scan_scope = str(folder)
        if self.scan_files is not None:
            scan_scope += f" • {human_count(len(self.scan_files))} visible/open file(s)"
        subtitle = QLabel(scan_scope)
        subtitle.setObjectName("MutedLabel")
        subtitle.setWordWrap(True)
        subtitle.setTextInteractionFlags(Qt.TextSelectableByMouse)
        subtitle.setSizePolicy(QSizePolicy.Ignored, QSizePolicy.Preferred)
        subtitle.setToolTip(scan_scope)
        title_box.addWidget(title)
        title_box.addWidget(subtitle)

        self.scan_btn = QPushButton("Start Scan")
        self.scan_btn.setObjectName("BrightGreyButton")
        self.refresh_btn = QPushButton("Refresh")
        self.undo_btn = QPushButton("Undo")
        self.undo_btn.setEnabled(False)
        self.close_btn = QPushButton("Close")
        header.addWidget(self.scan_btn)
        header.addWidget(self.refresh_btn)
        header.addWidget(self.undo_btn)
        header.addWidget(self.close_btn)

        progress_row = QHBoxLayout()
        layout.addLayout(progress_row)

        self.progress_label = QLabel("Ready")
        self.progress_label.setObjectName("MutedLabel")
        self.progress_label.setMinimumWidth(0)
        self.progress_label.setSizePolicy(QSizePolicy.Ignored, QSizePolicy.Fixed)
        self.progress = QProgressBar()
        self.progress.setTextVisible(False)
        self.progress.setFixedHeight(12)
        self.progress.setFixedWidth(420)
        self.progress.setVisible(False)
        progress_row.addWidget(self.progress_label, stretch=1)
        progress_row.addWidget(self.progress)

        self.preview_panel = PreviewPanel("Select a duplicate to preview it here.")
        self.preview_panel.zoomRequested.connect(self.zoom_duplicate_preview)
        layout.addWidget(self.preview_panel)

        self.tree = FileTreeWidget()
        self.tree.return_renames = True
        self.tree.setColumnCount(10)
        self.tree.setHeaderLabels([
            "File / Group", "Kind", "Confidence", "Damage Check", "Size",
            "Duration", "Sample Rate", "Resolution", "Location", "Details",
        ])
        self.tree.setRootIsDecorated(False)
        self.tree.setAlternatingRowColors(True)
        self.tree.setSelectionMode(QAbstractItemView.ExtendedSelection)
        self.tree.setSelectionBehavior(QAbstractItemView.SelectRows)
        self.tree.setEditTriggers(QAbstractItemView.NoEditTriggers)
        self.tree.setAllColumnsShowFocus(True)
        self.tree.setTextElideMode(Qt.ElideNone)
        self.tree.setUniformRowHeights(True)
        self.tree.setAnimated(False)
        self.tree.header().setSectionsMovable(True)
        self.tree.header().setStretchLastSection(False)
        self.tree.header().setMinimumSectionSize(72)
        for column in range(10):
            self.tree.header().setSectionResizeMode(column, QHeaderView.Interactive)
        self.tree.setColumnWidth(0, 360)
        self.tree.setColumnWidth(1, 115)
        self.tree.setColumnWidth(2, 105)
        self.tree.setColumnWidth(3, 145)
        self.tree.setColumnWidth(4, 95)
        self.tree.setColumnWidth(5, 90)
        self.tree.setColumnWidth(6, 115)
        self.tree.setColumnWidth(7, 115)
        self.tree.setColumnWidth(8, 160)
        self.tree.setColumnWidth(9, 280)
        restore_tree_header_state(self.tree, "duplicate_v3")
        self.tree.header().setStretchLastSection(False)
        connect_tree_header_persistence(self.tree, "duplicate_v3")
        self.tree.setContextMenuPolicy(Qt.CustomContextMenu)
        self.tree.customContextMenuRequested.connect(self.open_context_menu)
        self.tree.disclosurePressed.connect(self.toggle_duplicate_header)
        self.tree.itemDoubleClicked.connect(self.open_tree_item)
        self.tree.itemSelectionChanged.connect(self.update_duplicate_preview)
        self.tree.deletePressed.connect(self.move_selected_to_trash)
        self.tree.undoPressed.connect(self.undo_trash)
        self.tree.redoPressed.connect(self.redo_trash)
        self.tree.openPressed.connect(self.open_current_item)
        self.tree.previewPressed.connect(self.preview_current_item)
        self.tree.reviewStepPressed.connect(self.open_adjacent_file)
        self.tree.playPausePressed.connect(self.toggle_active_preview_playback)
        self.tree.renamePressed.connect(self.rename_current_item)
        self.tree.blankClicked.connect(self.clear_duplicate_selection)
        self.tree.itemChanged.connect(self.on_item_changed)
        layout.addWidget(self.tree, stretch=1)

        self.scan_btn.clicked.connect(self.handle_scan_button)
        self.refresh_btn.clicked.connect(self.refresh_clean_groups)
        self.undo_btn.clicked.connect(self.undo_trash)
        self.close_btn.clicked.connect(self.close)
        self.preview_shortcut = QShortcut(QKeySequence(Qt.Key_Space), self)
        # Space belongs to the active window: main window opens preview; cinema
        # dialog toggles playback with its own WindowShortcut.
        self.preview_shortcut.setContext(Qt.WindowShortcut)
        self.preview_shortcut.activated.connect(self.trigger_preview_shortcut)
        configure_settled_window_geometry(self, "duplicate_scan", QSize(1220, 760))

    def trigger_preview_shortcut(self):
        if self.renaming_item is not None:
            return
        if self.tree.state() == QAbstractItemView.EditingState:
            return
        self.preview_current_item()

    def start_scan(self):
        self.restore_active_review()
        self.close_after_scan_stops = False
        self.partial_results_timer.stop()
        self.pending_partial_items = None
        self.pending_partial_signature = None
        self.rendered_partial_signature = None
        self.last_partial_apply_at = 0.0
        self.scan_btn.setEnabled(True)
        self.scan_btn.setText("Terminate")
        self.close_btn.setEnabled(False)
        self.refresh_btn.setEnabled(True)
        self.group_items = {}
        self.group_fingerprints = {}
        self.user_collapsed_group_ids.clear()
        self.user_collapsed_subgroups.clear()
        self.all_dup_items = []
        self.dup_items_by_path = defaultdict(list)
        self.live_metadata_cache = {}
        self.live_health_cache = {}
        self.cleaned_group_items = {}
        self.deleted_dup_items_by_path = defaultdict(list)
        self.suppressed_paths = set()
        self.undo_stack = []
        self.redo_stack = []
        self.update_undo_button()
        self.set_preview_navigation_active(False)
        self.tree.clear()
        self.group_header_items.clear()
        self.progress.setRange(0, 0)
        self.progress.setValue(0)
        self.progress.setVisible(True)
        self.scan_progress_text = "Finding files to check…"
        self.progress_label.setText(self.scan_progress_text)

        self.worker = DuplicateWorker(self.folder, deep_media=True, scan_files=self.scan_files)
        self.worker.setStackSize(32 * 1024 * 1024)
        self.worker.progress.connect(self.on_progress)
        self.worker.partial.connect(self.on_partial_results)
        self.worker.metadata_ready.connect(self.on_duplicate_metadata_ready)
        self.worker.health_ready.connect(self.on_duplicate_health_ready)
        self.worker.results_ready.connect(self.on_finished)
        self.worker.failed.connect(self.on_failed)
        self.worker.cancelled.connect(self.on_cancelled)
        self.worker.start()

    def signal_worker(self) -> Optional[DuplicateWorker]:
        sender = self.sender()
        if isinstance(sender, DuplicateWorker):
            return sender
        return self.worker

    def finish_scan_controls(self):
        self.scan_btn.setEnabled(True)
        self.scan_btn.setText("Start Scan")
        self.close_btn.setEnabled(True)
        self.refresh_btn.setEnabled(True)
        self.progress.setVisible(False)

    def on_progress(self, text: str, value: int):
        self.scan_progress_text = text
        set_elided_label_text(
            self.progress_label,
            f"{text}  |  Found {human_count(len(self.group_items))} group(s) / {human_count(len(self.all_dup_items))} file(s)",
        )
        if value < 0:
            if self.progress.minimum() != 0 or self.progress.maximum() != 0:
                self.progress.setRange(0, 0)
        else:
            if self.progress.minimum() != 0 or self.progress.maximum() != 100:
                self.progress.setRange(0, 100)
            self.progress.setValue(max(0, min(100, value)))

    def on_partial_results(self, items: List[DupItem]):
        if self.suppressed_paths:
            items = [item for item in items if item.file not in self.suppressed_paths]
        self.apply_live_health(items)
        self.pending_partial_items = items
        self.pending_partial_signature = self.duplicate_partial_signature(items)
        elapsed_ms = int((time.monotonic() - self.last_partial_apply_at) * 1000)
        row_count = len(items) + sum(len(group) for group in self.cleaned_group_items.values())
        interval_ms = self.partial_update_interval_ms(row_count)
        first_render = self.tree.topLevelItemCount() == 0 and self.last_partial_apply_at == 0.0
        if elapsed_ms >= interval_ms or first_render:
            self.apply_pending_partial_results()
        elif not self.partial_results_timer.isActive():
            self.partial_results_timer.start(max(120, interval_ms - elapsed_ms))

    def on_duplicate_metadata_ready(self, path: Path, meta: MediaMeta):
        self.live_metadata_cache[path] = meta
        affected_groups = set()
        path_key = normalized_folder_path(path)
        for dup in self.dup_items_by_path.get(path_key, []):
            apply_duplicate_metadata(dup, meta)
            affected_groups.add(dup.group)

        if affected_groups:
            self.pending_metadata_group_ids.update(affected_groups)
            if not self.metadata_rows_timer.isActive():
                self.metadata_rows_timer.start(90)

        if getattr(self.preview_panel, "current_path", None) == path:
            self.preview_panel.on_metadata_loaded(path, meta)

    def apply_live_health(self, items: Iterable[DupItem]):
        for dup in items:
            result = self.live_health_cache.get(normalized_folder_path(dup.file))
            if result is not None:
                dup.health, dup.health_issue, dup.health_details = result

    def on_duplicate_health_ready(self, path: Path, result: object):
        if not isinstance(result, tuple) or len(result) != 3:
            return
        health_result = tuple(str(value or "") for value in result)
        path_key = normalized_folder_path(path)
        self.live_health_cache[path_key] = health_result
        affected_groups: set[int] = set()
        candidates: List[DupItem] = []
        candidates.extend(self.dup_items_by_path.get(path_key, []))
        if self.pending_partial_items is not None:
            candidates.extend(
                dup
                for dup in self.pending_partial_items
                if normalized_folder_path(dup.file) == path_key
            )
        seen: set[int] = set()
        for dup in candidates:
            if id(dup) in seen:
                continue
            seen.add(id(dup))
            dup.health, dup.health_issue, dup.health_details = health_result
            affected_groups.add(dup.group)
        if affected_groups:
            self.pending_metadata_group_ids.update(affected_groups)
            if not self.metadata_rows_timer.isActive():
                self.metadata_rows_timer.start(40)

    def flush_duplicate_metadata_rows(self):
        if not self.pending_metadata_group_ids:
            return
        # Updating every row for every metadata callback makes a large scanner
        # tree spend most of its time repainting. Keep each GUI turn bounded.
        group_ids = set()
        for group_id in self.pending_metadata_group_ids:
            group_ids.add(group_id)
            if len(group_ids) >= 8:
                break
        self.pending_metadata_group_ids.difference_update(group_ids)
        self.refresh_duplicate_metadata_rows(group_ids)
        if self.pending_metadata_group_ids:
            self.metadata_rows_timer.start(55)

    def duplicate_partial_signature(self, items: List[DupItem]) -> Tuple[int, int, int]:
        checksum = 0
        groups = set()
        for item in items:
            groups.add(item.group)
            checksum = (checksum * 1315423911 + item.group) & 0xFFFFFFFF
            checksum ^= hash(normalized_folder_path(item.file)) & 0xFFFFFFFF
        return (len(items), len(groups), checksum)

    def partial_update_interval_ms(self, row_count: int) -> int:
        if row_count > 5000:
            return 2500
        if row_count > 2500:
            return 2000
        if row_count > 1200:
            return 1500
        if row_count > 500:
            return 1000
        if row_count > 150:
            return 600
        return 240

    def apply_pending_partial_results(self):
        if self.pending_partial_items is None:
            return
        items = [item for item in self.pending_partial_items if item.file not in self.suppressed_paths]
        self.apply_live_health(items)
        for item in items:
            meta = self.live_metadata_cache.get(item.file)
            if meta is not None:
                apply_duplicate_metadata(item, meta)
        signature = self.pending_partial_signature or self.duplicate_partial_signature(items)
        self.pending_partial_items = None
        self.pending_partial_signature = None
        if signature == self.rendered_partial_signature:
            return
        self.populate_tree(items, preserve_selection=True)
        self.rendered_partial_signature = signature
        self.last_partial_apply_at = time.monotonic()
        set_elided_label_text(
            self.progress_label,
            f"{self.scan_progress_text}  |  Found {human_count(len(self.group_items))} group(s) / {human_count(len(self.all_dup_items))} file(s)",
        )

    def on_finished(self, items: List[DupItem]):
        worker = self.signal_worker()
        items = [item for item in items if item.file not in self.suppressed_paths]
        self.apply_live_health(items)
        for item in items:
            meta = self.live_metadata_cache.get(item.file)
            if meta is not None:
                apply_duplicate_metadata(item, meta)
        self.partial_results_timer.stop()
        self.pending_partial_items = None
        self.pending_partial_signature = None
        self.finish_scan_controls()
        self.retire_worker(worker)
        self.populate_tree(items, preserve_selection=True)
        self.rendered_partial_signature = self.duplicate_partial_signature(items)
        self.progress_label.setText(
            f"Found {human_count(len(self.group_items))} group(s) / {human_count(len(items))} file(s)"
        )
        self.update_undo_button()
        self.maybe_close_after_scan_stops()

    def on_failed(self, message: str):
        worker = self.signal_worker()
        self.partial_results_timer.stop()
        self.pending_partial_items = None
        self.pending_partial_signature = None
        self.finish_scan_controls()
        self.retire_worker(worker)
        self.progress_label.setText("Scan failed")
        extra = ""
        if getattr(sys, "frozen", False):
            extra = (
                "\n\nDeep video and audio matching requires the FFmpeg and ffprobe command-line "
                "tools. They are not included in this local QA build."
            )
        QMessageBox.warning(self, "Duplicate scan failed", message + extra)
        self.maybe_close_after_scan_stops()

    def on_cancelled(self):
        worker = self.signal_worker()
        self.partial_results_timer.stop()
        self.pending_partial_items = None
        self.pending_partial_signature = None
        self.finish_scan_controls()
        self.retire_worker(worker)
        self.progress_label.setText(
            f"Scan terminated  |  Found {human_count(len(self.group_items))} group(s) / "
            f"{human_count(len(self.all_dup_items))} file(s) kept"
        )
        self.update_undo_button()
        self.maybe_close_after_scan_stops()

    def normalize_duplicate_items(self, items: List[DupItem]) -> Tuple[List[DupItem], Dict[int, List[DupItem]]]:
        # Defensive UI-side coalescing: even a stale/third-party worker payload
        # cannot place the same path under two different headers.
        group_parent: Dict[int, int] = {}

        def find_group(group_id: int) -> int:
            group_parent.setdefault(group_id, group_id)
            while group_parent[group_id] != group_id:
                group_parent[group_id] = group_parent[group_parent[group_id]]
                group_id = group_parent[group_id]
            return group_id

        def union_groups(left: int, right: int):
            left_root = find_group(left)
            right_root = find_group(right)
            if left_root == right_root:
                return
            canonical = min(left_root, right_root)
            group_parent[left_root] = canonical
            group_parent[right_root] = canonical

        groups_by_path: Dict[str, set[int]] = defaultdict(set)
        for item in items:
            groups_by_path[normalized_folder_path(item.file)].add(item.group)
            find_group(item.group)
        for memberships in groups_by_path.values():
            ordered_memberships = sorted(memberships)
            for group_id in ordered_memberships[1:]:
                union_groups(ordered_memberships[0], group_id)
        for item in items:
            item.group = find_group(item.group)

        deduped_items: List[DupItem] = []
        seen_rows = set()
        existing_rows: Dict[str, bool] = {}

        def row_exists(item: DupItem) -> bool:
            key = normalized_folder_path(item.file)
            exists = existing_rows.get(key)
            if exists is None:
                exists = item.file.exists()
                existing_rows[key] = exists
            return exists

        incoming_counts: Dict[int, int] = defaultdict(int)
        for item in items:
            if item.file in self.suppressed_paths:
                continue
            key = normalized_folder_path(item.file)
            if key in seen_rows or not row_exists(item):
                continue
            seen_rows.add(key)
            deduped_items.append(item)
            incoming_counts[item.group] += 1

        for group_id in list(self.cleaned_group_items):
            if incoming_counts.get(group_id, 0) >= 2:
                self.cleaned_group_items.pop(group_id, None)
                continue
            cleaned = [
                item for item in self.cleaned_group_items[group_id]
                if row_exists(item) and item.file not in self.suppressed_paths
            ]
            if not cleaned:
                self.cleaned_group_items.pop(group_id, None)
                continue
            self.cleaned_group_items[group_id] = cleaned
            for item in cleaned:
                key = normalized_folder_path(item.file)
                if key not in seen_rows:
                    seen_rows.add(key)
                    deduped_items.append(item)

        groups: Dict[int, List[DupItem]] = defaultdict(list)
        for item in deduped_items:
            groups[item.group].append(item)
        valid_group_ids = {
            group_id
            for group_id, group in groups.items()
            if len(group) >= 2 or group_id in self.cleaned_group_items
        }
        deduped_items = [item for item in deduped_items if item.group in valid_group_ids]
        groups = defaultdict(list, {
            group_id: group
            for group_id, group in groups.items()
            if group_id in valid_group_ids
        })
        for group_id in list(groups):
            group = groups[group_id]
            has_excerpt = duplicate_group_has_meaningful_excerpt(group)
            groups[group_id] = sorted(
                group,
                key=lambda item: duplicate_group_item_sort_key(item, group, has_excerpt),
            )
        deduped_items = order_duplicate_items(
            item for item in deduped_items if item.group in valid_group_ids
        )
        return deduped_items, groups

    def duplicate_group_fingerprint(self, group: List[DupItem]) -> Tuple:
        return tuple(sorted(
            (
                normalized_folder_path(dup.file),
                dup.kind,
                dup.confidence,
                dup.details,
                dup.source_evidence,
                dup.duration_seconds,
                dup.sample_rate_hz,
                dup.width,
                dup.height,
                dup.quality_score,
                dup.health,
                dup.health_issue,
                dup.health_details,
            )
            for dup in group
        ))

    def create_duplicate_group_item(self, group_id: int, group: List[DupItem], expanded: bool = True) -> QTreeWidgetItem:
        expanded = expanded and group_id not in self.user_collapsed_group_ids
        header = QTreeWidgetItem([self.group_header_text(group_id, group, expanded=expanded)] + [""] * 9)
        header.setData(0, self.ROLE_KIND, "group")
        header.setData(0, self.ROLE_GROUP, group_id)
        header.setTextAlignment(0, Qt.AlignLeft | Qt.AlignVCenter)
        for column in range(self.tree.columnCount()):
            header.setSizeHint(column, QSize(0, 32))
            header.setToolTip(column, header.text(0))
            font = header.font(column)
            font.setBold(True)
            header.setFont(column, font)
        header.setFirstColumnSpanned(True)

        cleaned_group = len(group) < 2
        subgroups = self.duplicate_subgroups(group)
        if subgroups:
            for subgroup_text, subgroup_items in subgroups:
                subheader = QTreeWidgetItem([""] * 10)
                subheader.setData(0, self.ROLE_KIND, "subgroup")
                subheader.setData(0, self.ROLE_GROUP, group_id)
                subheader.setData(0, self.ROLE_SUBGROUP, subgroup_text)
                subheader.setTextAlignment(0, Qt.AlignLeft | Qt.AlignVCenter)
                for column in range(self.tree.columnCount()):
                    subheader.setSizeHint(column, QSize(0, 28))
                    subheader.setToolTip(column, subgroup_text)
                header.addChild(subheader)
                subheader.setFirstColumnSpanned(True)
                subgroup_cleaned = len(subgroup_items) < 2
                for dup in subgroup_items:
                    subheader.addChild(self.duplicate_child_item(dup, group=subgroup_items, cleaned=subgroup_cleaned))
                subgroup_key = (group_id, subgroup_text)
                subheader.setExpanded(subgroup_key not in self.user_collapsed_subgroups)
                self.update_subgroup_header_item(subheader)
                self.style_duplicate_subheader(subheader, subgroup_cleaned)
        else:
            for dup in group:
                header.addChild(self.duplicate_child_item(dup, group=group, cleaned=cleaned_group))

        header.setExpanded(expanded)
        self.update_group_header_item(header)
        self.style_duplicate_header(header, cleaned_group)
        return header

    def expand_new_duplicate_header(self, header: QTreeWidgetItem):
        if header is None or header.treeWidget() is not self.tree:
            return
        group_id = self.tree_item_group(header)
        if group_id is None or group_id in self.user_collapsed_group_ids:
            return
        header.setExpanded(True)
        self.update_group_header_item(header)
        for index in range(header.childCount()):
            child = header.child(index)
            if child.data(0, self.ROLE_KIND) == "subgroup":
                subgroup_text = str(child.data(0, self.ROLE_SUBGROUP) or "")
                if (group_id, subgroup_text) in self.user_collapsed_subgroups:
                    continue
                child.setExpanded(True)
                self.update_subgroup_header_item(child)

    def reconcile_duplicate_tree(
        self,
        deduped_items: List[DupItem],
        new_groups: Dict[int, List[DupItem]],
        selected_paths: List[Path],
        current_path: Optional[Path],
        scroll_value: int,
    ):
        old_groups = dict(self.group_items)
        # This index is maintained whenever headers are inserted/removed. Do not
        # traverse thousands of native QTreeWidget items on every partial signal.
        old_headers = dict(self.group_header_items)
        new_fingerprints = {
            group_id: self.duplicate_group_fingerprint(group)
            for group_id, group in new_groups.items()
        }
        old_fingerprints = self.group_fingerprints or {
            group_id: self.duplicate_group_fingerprint(group)
            for group_id, group in old_groups.items()
        }
        changed = {
            group_id
            for group_id in set(old_groups) | set(new_groups)
            if old_fingerprints.get(group_id) != new_fingerprints.get(group_id)
        }
        if not changed:
            self.all_dup_items = deduped_items
            self.group_items = defaultdict(list, new_groups)
            self.group_fingerprints = new_fingerprints
            return

        changed_paths = {
            dup.file
            for group_id in changed
            for dup in old_groups.get(group_id, []) + new_groups.get(group_id, [])
        }
        restore_selection = bool(current_path in changed_paths or any(path in changed_paths for path in selected_paths))
        previous_block = self.tree.blockSignals(True)
        previous_updates = self.tree.updatesEnabled()
        self.tree.setUpdatesEnabled(False)
        try:
            for group_id in changed:
                header = old_headers.get(group_id)
                if header is not None:
                    index = self.tree.indexOfTopLevelItem(header)
                    if index >= 0:
                        self.tree.takeTopLevelItem(index)
                self.group_header_items.pop(group_id, None)

            self.all_dup_items = deduped_items
            self.group_items = defaultdict(list, new_groups)
            self.group_fingerprints = new_fingerprints
            ordered_group_ids = sorted(group_id for group_id in new_groups if group_id not in changed)
            for group_id in sorted(changed):
                group = new_groups.get(group_id)
                if not group:
                    continue
                header = self.create_duplicate_group_item(
                    group_id,
                    group,
                    group_id not in self.user_collapsed_group_ids,
                )
                insert_at = bisect.bisect_left(ordered_group_ids, group_id)
                self.tree.insertTopLevelItem(insert_at, header)
                self.group_header_items[group_id] = header
                self.expand_new_duplicate_header(header)
                ordered_group_ids.insert(insert_at, group_id)

            if restore_selection:
                self.restore_tree_selection(selected_paths, current_path)
            self.tree.verticalScrollBar().setValue(scroll_value)
        finally:
            self.tree.blockSignals(previous_block)
            self.tree.setUpdatesEnabled(previous_updates)
            self.tree.viewport().update()

    def load_next_duplicate_tree_chunk(self):
        """Build a large first result progressively without blocking input."""
        if not self._duplicate_tree_loading:
            return
        started = time.monotonic()
        added = 0
        previous_block = self.tree.blockSignals(True)
        previous_updates = self.tree.updatesEnabled()
        self.tree.setUpdatesEnabled(False)
        try:
            while self._duplicate_tree_pending_group_ids:
                group_id = self._duplicate_tree_pending_group_ids.popleft()
                if group_id in self.group_header_items:
                    continue
                group = self.group_items.get(group_id)
                if not group:
                    continue
                header = self.create_duplicate_group_item(group_id, group, True)
                self.tree.addTopLevelItem(header)
                self.expand_new_duplicate_header(header)
                self.group_header_items[group_id] = header
                self.group_fingerprints[group_id] = self.duplicate_group_fingerprint(group)
                added += 1
                if (
                    added >= 12
                    or time.monotonic() - started >= SCANNER_GUI_SLICE_SECONDS
                ):
                    break
        finally:
            self.tree.blockSignals(previous_block)
            self.tree.setUpdatesEnabled(previous_updates)
            self.tree.viewport().update()
        if self._duplicate_tree_pending_group_ids:
            self.duplicate_tree_loader_timer.start(0)
            return
        self._duplicate_tree_loading = False
        latest = self._duplicate_tree_latest_items
        self._duplicate_tree_latest_items = None
        if latest is not None:
            # Results/health may have advanced while the initial rows were being
            # streamed. Reconcile only the changed, now-existing headers.
            QTimer.singleShot(0, lambda items=latest: self.populate_tree(items, preserve_selection=True))

    def update_large_duplicate_tree_load(
        self,
        deduped_items: List[DupItem],
        groups: Dict[int, List[DupItem]],
    ):
        """Retarget an in-flight first render to the newest scanner payload."""
        new_group_ids = set(groups)
        for group_id in list(self.group_header_items):
            if group_id in new_group_ids:
                continue
            header = self.group_header_items.pop(group_id, None)
            if header is not None:
                index = self.tree.indexOfTopLevelItem(header)
                if index >= 0:
                    self.tree.takeTopLevelItem(index)
            self.group_fingerprints.pop(group_id, None)
        self.all_dup_items = deduped_items
        self.group_items = defaultdict(list, groups)
        self._duplicate_tree_pending_group_ids = deque(
            group_id for group_id in sorted(groups) if group_id not in self.group_header_items
        )
        self._duplicate_tree_latest_items = list(deduped_items)
        self.rebuild_duplicate_path_index()
        if self._duplicate_tree_pending_group_ids and not self.duplicate_tree_loader_timer.isActive():
            self.duplicate_tree_loader_timer.start(0)

    def populate_tree(self, items: List[DupItem], preserve_selection: bool = False):
        selected_paths = self.selected_paths() if preserve_selection else []
        current_path = self.current_file_path() if preserve_selection else None
        scroll_value = self.tree.verticalScrollBar().value()
        deduped_items, groups = self.normalize_duplicate_items(items)

        if self._duplicate_tree_loading:
            self.update_large_duplicate_tree_load(deduped_items, groups)
            return

        if preserve_selection and self.tree.topLevelItemCount() > 0:
            self.reconcile_duplicate_tree(deduped_items, groups, selected_paths, current_path, scroll_value)
        else:
            previous_block = self.tree.blockSignals(True)
            previous_updates = self.tree.updatesEnabled()
            self.tree.setUpdatesEnabled(False)
            try:
                self.tree.clear()
                self.group_header_items.clear()
                self.all_dup_items = deduped_items
                self.group_items = defaultdict(list, groups)
                self.group_fingerprints = {
                    group_id: self.duplicate_group_fingerprint(group)
                    for group_id, group in groups.items()
                }
                progressive_first_load = preserve_selection and len(groups) > 180
                if progressive_first_load:
                    self.group_fingerprints.clear()
                    self._duplicate_tree_loading = True
                    self._duplicate_tree_pending_group_ids = deque(sorted(groups))
                    self._duplicate_tree_latest_items = None
                else:
                    for group_id in sorted(groups):
                        header = self.create_duplicate_group_item(group_id, groups[group_id], True)
                        self.tree.addTopLevelItem(header)
                        self.expand_new_duplicate_header(header)
                        self.group_header_items[group_id] = header
                if preserve_selection:
                    self.restore_tree_selection(selected_paths, current_path)
                    self.tree.verticalScrollBar().setValue(scroll_value)
            finally:
                self.tree.blockSignals(previous_block)
                self.tree.setUpdatesEnabled(previous_updates)
                self.tree.viewport().update()

            if self._duplicate_tree_loading:
                self.load_next_duplicate_tree_chunk()

        self.rebuild_duplicate_path_index()

        if preserve_selection:
            selected_path = self.current_file_path()
            if (
                selected_path
                and selected_path.exists()
                and getattr(self.preview_panel, "current_path", None) != selected_path
            ):
                self.update_duplicate_preview()

    def rebuild_duplicate_path_index(self):
        index: Dict[str, List[DupItem]] = defaultdict(list)
        for dup in self.all_dup_items:
            index[normalized_folder_path(dup.file)].append(dup)
        self.dup_items_by_path = index

    def restore_tree_selection(self, selected_paths: List[Path], current_path: Optional[Path]):
        selected_set = set(selected_paths)
        target_item = None
        self.tree.clearSelection()
        for item in self.file_items_in_order():
            path = self.tree_item_path(item)
            if path in selected_set:
                item.setSelected(True)
            if current_path and path == current_path:
                target_item = item
        if target_item is None and selected_set:
            target_item = next((item for item in self.file_items_in_order() if self.tree_item_path(item) in selected_set), None)
        if target_item:
            self.tree.setCurrentItem(target_item)

    def refresh_clean_groups(self):
        if self.pending_partial_items is not None:
            self.apply_pending_partial_results()
        existing_by_group: Dict[int, int] = defaultdict(int)
        for item in self.all_dup_items:
            if item.file.exists():
                existing_by_group[item.group] += 1
        all_groups = {item.group for item in self.all_dup_items}
        removable = {group for group in all_groups if existing_by_group[group] < 2}
        self.all_dup_items = [item for item in self.all_dup_items if item.group not in removable]
        for group_id in removable:
            self.cleaned_group_items.pop(group_id, None)
        self.refresh_tree_from_items(select_path=self.current_active_file_path)
        self.progress_label.setText(f"Removed {human_count(len(removable))} cleaned group(s)")

    def compact_duplicate_label(self, text: str, limit: int = 58) -> str:
        text = re.sub(r"\s+", " ", text).strip(" -_[]()")
        if len(text) <= limit:
            return text
        head = max(8, (limit - 3) // 2)
        tail = max(8, limit - 3 - head)
        return f"{text[:head]}...{text[-tail:]}"

    def duplicate_subgroup_label(self, items: List[DupItem]) -> str:
        stems = [strip_order_prefixes(item.file.stem) for item in items if item.file]
        if not stems:
            return "Linked files"
        prefix = os.path.commonprefix(stems).strip(" -_[]()")
        if len(prefix) >= 10:
            return self.compact_duplicate_label(prefix)
        return self.compact_duplicate_label(stems[0])

    def duplicate_subgroup_text(self, index: int, items: List[DupItem], kinds: Iterable[str], fallback: str = "") -> str:
        total_size = 0
        for item in items:
            try:
                total_size += item.file.stat().st_size
            except OSError:
                pass
        ordered_kinds = sorted(set(kinds), key=duplicate_evidence_rank, reverse=True)
        kind_text = " + ".join(ordered_kinds[:2]) if ordered_kinds else (fallback or "Linked match")
        label = self.duplicate_subgroup_label(items)
        return f"Match Set {index} ({len(items)} files)  |  {kind_text}  |  {self.group_location_text(items)}  |  {human_size(total_size)}  |  {label}"

    def relative_location_text(self, path: Path) -> str:
        return str(path.parent)

    def group_location_text(self, group: List[DupItem]) -> str:
        folders = {
            normalized_folder_path(item.file.parent)
            for item in group
            if item.file and item.file.exists()
        }
        if len(folders) <= 1:
            return "Same folder"
        return f"Different folders: {len(folders)}"

    def duplicate_subgroups(self, group: List[DupItem]) -> List[Tuple[str, List[DupItem]]]:
        if len(group) < 3:
            return []

        full_paths = {normalized_folder_path(item.file) for item in group if item.file.exists()}
        evidence_members: Dict[int, List[DupItem]] = defaultdict(list)
        evidence_kinds: Dict[int, set] = defaultdict(set)
        evidence_details: Dict[int, set] = defaultdict(set)

        for dup in group:
            for evidence_id, kind, detail in dup.source_evidence:
                evidence_members[evidence_id].append(dup)
                if kind:
                    evidence_kinds[evidence_id].add(kind)
                if detail:
                    evidence_details[evidence_id].add(detail)

        candidates = []
        for evidence_id, members in evidence_members.items():
            unique_by_path: Dict[str, DupItem] = {}
            for member in members:
                if member.file.exists():
                    unique_by_path[normalized_folder_path(member.file)] = member
            paths = set(unique_by_path)
            if len(paths) < 2 or paths == full_paths:
                continue
            kinds = evidence_kinds.get(evidence_id, set())
            rank = max([duplicate_evidence_rank(kind) for kind in kinds] or [10])
            label_key = self.duplicate_subgroup_label(list(unique_by_path.values())).casefold()
            candidates.append((rank, len(paths), label_key, evidence_id, list(unique_by_path.values()), kinds))

        if not candidates:
            return []

        candidates.sort(key=lambda value: (-value[0], value[1], value[2], value[3]))
        assigned: set = set()
        subgroups: List[Tuple[str, List[DupItem]]] = []

        for _rank, _count, _label, _evidence_id, members, kinds in candidates:
            available = [member for member in members if normalized_folder_path(member.file) not in assigned]
            if len(available) < 2:
                continue
            has_excerpt = duplicate_group_has_meaningful_excerpt(available)
            available = sorted(
                available,
                key=lambda item: duplicate_group_item_sort_key(item, available, has_excerpt),
            )
            for member in available:
                assigned.add(normalized_folder_path(member.file))
            text = self.duplicate_subgroup_text(len(subgroups) + 1, available, kinds)
            subgroups.append((text, available))

        remaining = [
            dup
            for dup in group
            if normalized_folder_path(dup.file) not in assigned and dup.file.exists()
        ]
        # A subgroup must itself be a duplicate set. If the evidence partition
        # leaves any singleton behind, show the parent group flat instead of
        # inventing a misleading one-file match set.
        if remaining:
            return []

        if len(subgroups) < 2 and sum(len(items) for _text, items in subgroups) == len(group):
            return []
        return subgroups

    def duplicate_metric_badges(self, dup: DupItem, group: List[DupItem]) -> Dict[str, str]:
        if len(group) < 2:
            return {}

        sizes = []
        durations = []
        sample_rates = []
        pixels = []
        for item in group:
            try:
                sizes.append(item.file.stat().st_size)
            except OSError:
                pass
            if item.duration_seconds:
                durations.append(item.duration_seconds)
            if item.sample_rate_hz:
                sample_rates.append(item.sample_rate_hz)
            if item.width and item.height:
                pixels.append(item.width * item.height)

        def badge(value: float, values: List[float], higher_is_better: bool = True, tolerance: float = 0.0) -> str:
            if not value or len(values) < 2:
                return ""
            if min(values) == max(values) or max(values) - min(values) <= tolerance:
                return ""
            best = max(values) if higher_is_better else min(values)
            worst = min(values) if higher_is_better else max(values)
            if abs(value - best) <= tolerance:
                return "▲ "
            if abs(value - worst) <= tolerance:
                return "▼ "
            midpoint = sum(values) / len(values)
            return "▲ " if (value >= midpoint if higher_is_better else value <= midpoint) else "▼ "

        try:
            size = dup.file.stat().st_size
        except OSError:
            size = 0
        duration_labels = {item.duration for item in group if item.duration}
        sample_rate_labels = {item.sample_rate for item in group if item.sample_rate}
        resolution_labels = {item.resolution for item in group if item.resolution}
        return {
            "size": badge(float(size), [float(v) for v in sizes]),
            "duration": "" if len(duration_labels) <= 1 else badge(
                float(round(dup.duration_seconds)),
                [float(round(v)) for v in durations],
                tolerance=1.0,
            ),
            "sample_rate": "" if len(sample_rate_labels) <= 1 else badge(
                float(dup.sample_rate_hz), [float(v) for v in sample_rates]
            ),
            "resolution": "" if len(resolution_labels) <= 1 else badge(
                float(dup.width * dup.height), [float(v) for v in pixels]
            ),
        }

    def duplicate_child_item(self, dup: DupItem, group: Optional[List[DupItem]] = None, cleaned: bool = False) -> QTreeWidgetItem:
        child = QTreeWidgetItem([""] * 10)
        child.setData(0, self.ROLE_KIND, "file")
        child.setData(0, self.ROLE_GROUP, dup.group)
        child.setData(0, self.ROLE_PATH, str(dup.file))
        child.setFlags(child.flags() | Qt.ItemIsEditable)
        self.update_duplicate_child_values(child, dup, group or [])
        if cleaned:
            self.style_cleaned_duplicate_item(child)
        return child

    def update_duplicate_child_values(self, child: QTreeWidgetItem, dup: DupItem, group: List[DupItem]):
        try:
            size_text = human_size(dup.file.stat().st_size)
        except OSError:
            size_text = "?"
        quality = quality_summary_for_item(dup)
        is_recommended = bool(
            group
            and normalized_folder_path(group[0].file) == normalized_folder_path(dup.file)
            and dup.health == DUPLICATE_HEALTH_VERIFIED
        )
        if dup.health == DUPLICATE_HEALTH_VERIFIED:
            health_column_text = "Healthy"
            health_text = "Verified healthy"
        elif dup.health == DUPLICATE_HEALTH_DAMAGED:
            health_column_text = "Damaged"
            health_text = f"DAMAGED: {dup.health_issue or 'damage detected'}"
        elif dup.health == DUPLICATE_HEALTH_UNVERIFIED:
            health_column_text = "Review needed"
            health_text = f"Manual review needed: {dup.health_issue or 'could not fully verify'}"
        else:
            health_column_text = "Checking…"
            health_text = "Damage check running; this duplicate family remains deletion-locked"
        detail_parts = []
        if is_recommended:
            detail_parts.append("Recommended original")
        detail_parts.append(health_text)
        if dup.health_details and dup.health != DUPLICATE_HEALTH_VERIFIED:
            detail_parts.append(dup.health_details)
        if quality:
            detail_parts.append(quality)
        if dup.details:
            detail_parts.append(dup.details)
        details = "  |  ".join(detail_parts)
        badges = self.duplicate_metric_badges(dup, group)
        location = self.relative_location_text(dup.file)
        values = [
            dup.file.name,
            kind_for_path(dup.file),
            dup.confidence,
            health_column_text,
            f"{badges.get('size', '')}{size_text}",
            f"{badges.get('duration', '')}{dup.duration}",
            f"{badges.get('sample_rate', '')}{dup.sample_rate}",
            f"{badges.get('resolution', '')}{dup.resolution}",
            location,
            details,
        ]
        tooltip_values = [
            str(dup.file),
            kind_for_path(dup.file),
            dup.confidence,
            health_text + ((" — " + dup.health_details) if dup.health_details else ""),
            size_text,
            dup.duration,
            dup.sample_rate,
            dup.resolution,
            str(dup.file.parent),
            details,
        ]
        for column, value in enumerate(values):
            child.setText(column, value)
            child.setToolTip(column, tooltip_values[column])
        self.request_details_column_width(details)
        for column in range(self.tree.columnCount()):
            child.setData(column, Qt.ForegroundRole, None)
        name_font = child.font(0)
        name_font.setBold(False)
        child.setFont(0, name_font)
        for column in (self.SIZE_COLUMN, self.DURATION_COLUMN, self.SAMPLE_RATE_COLUMN, self.RESOLUTION_COLUMN):
            child.setData(column, Qt.ForegroundRole, None)
        self.style_duplicate_metric_badges(child)
        if dup.health == DUPLICATE_HEALTH_DAMAGED:
            child.setForeground(0, QColor("#ff9a9a"))
            child.setForeground(self.DAMAGE_COLUMN, QColor("#ff7777"))
            child.setForeground(self.DETAILS_COLUMN, QColor("#ff9a9a"))
        elif dup.health == DUPLICATE_HEALTH_UNVERIFIED:
            child.setForeground(0, QColor("#ffd38a"))
            child.setForeground(self.DAMAGE_COLUMN, QColor("#ffd38a"))
            child.setForeground(self.DETAILS_COLUMN, QColor("#ffd38a"))
        elif dup.health == DUPLICATE_HEALTH_VERIFIED:
            child.setForeground(self.DAMAGE_COLUMN, QColor("#91d18b"))
            if is_recommended:
                child.setForeground(0, QColor("#aee7b1"))
                child.setForeground(self.DETAILS_COLUMN, QColor("#aee7b1"))
                font = child.font(0)
                font.setBold(True)
                child.setFont(0, font)

    def refresh_duplicate_metadata_rows(self, group_ids: set[int]):
        selected_paths = self.selected_paths()
        current_path = self.current_file_path()
        scroll_value = self.tree.verticalScrollBar().value()
        selection_needs_restore = False
        previous_updates = self.tree.updatesEnabled()
        previous_block = self.tree.blockSignals(True)
        self.tree.setUpdatesEnabled(False)
        try:
            for group_id in group_ids:
                header = self.group_header_items.get(group_id)
                if header is None or self.tree.indexOfTopLevelItem(header) < 0:
                    continue
                group = self.group_items.get(group_id, [])
                has_excerpt = duplicate_group_has_meaningful_excerpt(group)
                group.sort(
                    key=lambda item: duplicate_group_item_sort_key(item, group, has_excerpt)
                )
                desired_paths = [normalized_folder_path(dup.file) for dup in group]
                current_paths = [
                    normalized_folder_path(path)
                    for path in self.descendant_file_paths(header)
                ]
                if desired_paths != current_paths:
                    group_paths = set(desired_paths) | set(current_paths)
                    selection_needs_restore = selection_needs_restore or bool(
                        (current_path and normalized_folder_path(current_path) in group_paths)
                        or any(normalized_folder_path(path) in group_paths for path in selected_paths)
                    )
                    top_index = self.tree.indexOfTopLevelItem(header)
                    expanded = group_id not in self.user_collapsed_group_ids
                    self.tree.takeTopLevelItem(top_index)
                    header = self.create_duplicate_group_item(group_id, group, expanded)
                    self.tree.insertTopLevelItem(top_index, header)
                    self.group_header_items[group_id] = header
                    if expanded:
                        self.expand_new_duplicate_header(header)
                    self.group_fingerprints[group_id] = self.duplicate_group_fingerprint(group)
                    continue
                by_path = {normalized_folder_path(dup.file): dup for dup in group}
                comparison_groups: Dict[str, List[DupItem]] = {}
                for _subgroup_text, subgroup_items in self.duplicate_subgroups(group):
                    for subgroup_dup in subgroup_items:
                        comparison_groups[normalized_folder_path(subgroup_dup.file)] = subgroup_items
                for child in self.descendant_file_items(header):
                    child_path = self.tree_item_path(child)
                    if child_path is None:
                        continue
                    path_key = normalized_folder_path(child_path)
                    dup = by_path.get(path_key)
                    if dup is not None:
                        self.update_duplicate_child_values(child, dup, comparison_groups.get(path_key, group))
                # Health and metadata callbacks usually keep the same members,
                # so the cheap in-place path must refresh the summary too.
                self.update_group_header_item(header)
                for child_index in range(header.childCount()):
                    child = header.child(child_index)
                    if child.data(0, self.ROLE_KIND) == "subgroup":
                        self.update_subgroup_header_item(child)
                self.group_fingerprints[group_id] = self.duplicate_group_fingerprint(group)
            # In-place text/colour updates preserve QTreeWidget selection.  A
            # full-tree traversal on every health callback was the dominant GUI
            # cost while a scanner populated results and a preview was playing.
            # Restore only when a selected group's header was actually replaced.
            if selection_needs_restore:
                self.restore_tree_selection(selected_paths, current_path)
                self.tree.verticalScrollBar().setValue(scroll_value)
        finally:
            self.tree.blockSignals(previous_block)
            self.tree.setUpdatesEnabled(previous_updates)
            self.tree.viewport().update()

    def style_duplicate_metric_badges(self, item: QTreeWidgetItem):
        for column in (self.SIZE_COLUMN, self.DURATION_COLUMN, self.SAMPLE_RATE_COLUMN, self.RESOLUTION_COLUMN):
            text = item.text(column)
            if text.startswith("▲"):
                item.setForeground(column, QColor("#91d18b"))
            elif text.startswith("▼"):
                item.setForeground(column, QColor("#e18b8b"))

    def style_duplicate_header(self, item: QTreeWidgetItem, cleaned: bool = False):
        base = QColor("#3b3c43") if not cleaned else QColor("#555966")
        foreground = QColor("#f2f2f6") if not cleaned else QColor("#c8cad3")
        brush = QBrush(base, Qt.BDiagPattern) if cleaned else QBrush(base)
        for column in range(self.tree.columnCount()):
            item.setBackground(column, brush)
            item.setForeground(column, foreground)
            font = item.font(column)
            font.setBold(True)
            item.setFont(column, font)

    def style_duplicate_subheader(self, item: QTreeWidgetItem, cleaned: bool = False):
        base = QColor("#31323a") if not cleaned else QColor("#51545f")
        foreground = QColor("#e7e7ed") if not cleaned else QColor("#c7c9d2")
        brush = QBrush(base, Qt.BDiagPattern) if cleaned else QBrush(base)
        for column in range(self.tree.columnCount()):
            item.setBackground(column, brush)
            item.setForeground(column, foreground)
            font = item.font(column)
            font.setBold(True)
            item.setFont(column, font)

    def style_cleaned_duplicate_item(self, item: QTreeWidgetItem):
        brush = QBrush(QColor("#484b55"), Qt.BDiagPattern)
        for column in range(self.tree.columnCount()):
            item.setBackground(column, brush)
            item.setForeground(column, QColor("#c9cad2"))

    def tree_item_path(self, item: Optional[QTreeWidgetItem]) -> Optional[Path]:
        if not item or item.data(0, self.ROLE_KIND) != "file":
            return None
        path_text = item.data(0, self.ROLE_PATH)
        return Path(path_text) if path_text else None

    def tree_item_group(self, item: Optional[QTreeWidgetItem]) -> Optional[int]:
        if not item:
            return None
        group = item.data(0, self.ROLE_GROUP)
        return int(group) if group is not None else None

    def descendant_file_items(self, item: Optional[QTreeWidgetItem]) -> List[QTreeWidgetItem]:
        if not item:
            return []
        items: List[QTreeWidgetItem] = []

        def collect(parent: QTreeWidgetItem):
            for child_index in range(parent.childCount()):
                child = parent.child(child_index)
                if self.tree_item_path(child):
                    items.append(child)
                else:
                    collect(child)

        collect(item)
        return items

    def visible_descendant_file_items(self, item: Optional[QTreeWidgetItem]) -> List[QTreeWidgetItem]:
        if not item:
            return []
        items: List[QTreeWidgetItem] = []

        def collect(parent: QTreeWidgetItem):
            for child_index in range(parent.childCount()):
                child = parent.child(child_index)
                if self.tree_item_path(child):
                    items.append(child)
                elif child.isExpanded():
                    collect(child)

        collect(item)
        return items

    def descendant_file_paths(self, item: Optional[QTreeWidgetItem]) -> List[Path]:
        paths: List[Path] = []
        for child in self.descendant_file_items(item):
            path = self.tree_item_path(child)
            if path and path.exists():
                paths.append(path)
        return paths

    def first_descendant_file_item(self, item: Optional[QTreeWidgetItem]) -> Optional[QTreeWidgetItem]:
        children = self.visible_descendant_file_items(item) or self.descendant_file_items(item)
        return children[0] if children else None

    def selected_paths(self) -> List[Path]:
        paths: List[Path] = []
        seen = set()
        for item in self.tree.selectedItems():
            if item.data(0, self.ROLE_KIND) == "group":
                group_paths = [self.tree_item_path(child) for child in self.visible_descendant_file_items(item)] if item.isExpanded() else []
                for path in group_paths:
                    if path and path not in seen:
                        paths.append(path)
                        seen.add(path)
                continue
            if item.data(0, self.ROLE_KIND) == "subgroup":
                for path in ([self.tree_item_path(child) for child in self.visible_descendant_file_items(item)] if item.isExpanded() else []):
                    if path and path not in seen:
                        paths.append(path)
                        seen.add(path)
                continue

            path = self.tree_item_path(item)
            if path and path not in seen:
                paths.append(path)
                seen.add(path)
        return paths

    def file_items_in_order(self) -> List[QTreeWidgetItem]:
        items: List[QTreeWidgetItem] = []
        for top_index in range(self.tree.topLevelItemCount()):
            header = self.tree.topLevelItem(top_index)
            if not header.isExpanded():
                continue
            items.extend(self.visible_descendant_file_items(header))
        return items

    def file_paths_in_order(self) -> List[Path]:
        return [path for item in self.file_items_in_order() if (path := self.tree_item_path(item)) is not None]

    def current_file_path(self) -> Optional[Path]:
        current = self.tree.currentItem()
        path = self.tree_item_path(current)
        if path:
            return path
        selected = self.selected_paths()
        return selected[0] if selected else None

    def rename_current_item(self):
        item = self.tree.currentItem()
        path = self.tree_item_path(item)
        if not item or not path:
            return
        self.renaming_item = item
        self.renaming_path = path
        self.tree.editItem(item, 0)

    def on_item_changed(self, item: QTreeWidgetItem, column: int):
        if self.rename_suppress:
            return
        if column != 0 or item is not self.renaming_item or self.renaming_path is None:
            return
        original = self.renaming_path
        self.renaming_item = None
        self.renaming_path = None
        new_name = item.text(0).strip()
        if not new_name or "/" in new_name or new_name in {".", ".."} or new_name == original.name:
            self.update_duplicate_file_row(item, original)
            return
        target = unique_path(original.with_name(new_name)) if original.with_name(new_name).exists() else original.with_name(new_name)
        try:
            original.rename(target)
        except (OSError, ValueError) as exc:
            self.progress_label.setText(f"Rename failed: {exc}")
            self.update_duplicate_file_row(item, original)
            return
        self.replace_path_references(original, target)
        self.update_duplicate_file_row(item, target)
        self.progress_label.setText(f"Renamed {original.name}")

    def update_duplicate_file_row(self, item: QTreeWidgetItem, path: Path):
        self.rename_suppress = True
        try:
            item.setText(0, path.name)
            item.setData(0, self.ROLE_PATH, str(path))
            item.setToolTip(0, str(path))
        finally:
            self.rename_suppress = False

    def refresh_tree_from_items(self, select_path: Optional[Path] = None, select_index: Optional[int] = None):
        self.populate_tree(self.all_dup_items)
        self.select_file_after_refresh(select_path, select_index)

    def select_file_after_refresh(self, select_path: Optional[Path] = None, select_index: Optional[int] = None):
        items = self.file_items_in_order()
        if not items:
            self.tree.clearSelection()
            self.preview_panel.reset()
            if self.quicklook_dialog and self.quicklook_dialog.isVisible():
                self.quicklook_dialog.close()
            return

        target_item = None
        if select_path is not None:
            for item in items:
                if self.tree_item_path(item) == select_path:
                    target_item = item
                    break

        if target_item is None and select_index is not None:
            target_item = items[max(0, min(select_index, len(items) - 1))]

        if target_item is None:
            target_item = items[0]

        self.tree.clearSelection()
        target_item.setSelected(True)
        self.tree.setCurrentItem(target_item)
        self.tree.scrollToItem(target_item)
        self.update_duplicate_preview()

    def group_header_text(self, group_id: int, group: List[DupItem], expanded: bool = True) -> str:
        total_size = 0
        for dup in group:
            try:
                total_size += dup.file.stat().st_size
            except OSError:
                pass
        first = group[0] if group else None
        kind = first.kind if first else "Group"
        confidence = first.confidence if first else ""
        marker = "▼" if expanded else "▶"
        verified = sum(item.health == DUPLICATE_HEALTH_VERIFIED for item in group)
        damaged = sum(item.health == DUPLICATE_HEALTH_DAMAGED for item in group)
        unverified = sum(item.health == DUPLICATE_HEALTH_UNVERIFIED for item in group)
        pending = sum(item.health == DUPLICATE_HEALTH_PENDING for item in group)
        if pending:
            safety = f"Safety checks pending: {pending}"
        else:
            safety_parts = [f"{verified} healthy"]
            if damaged:
                safety_parts.append(f"{damaged} damaged")
            if unverified:
                safety_parts.append(f"{unverified} manual review")
            safety = " / ".join(safety_parts)
        return (
            f"{marker} Duplicate Group {group_id} ({len(group)} files)  |  {kind}  |  "
            f"{confidence}  |  {safety}  |  {self.group_location_text(group)}  |  "
            f"{human_size(total_size)}"
        )

    def update_group_header_item(self, item: Optional[QTreeWidgetItem]):
        if not item or item.data(0, self.ROLE_KIND) != "group":
            return
        group_id = self.tree_item_group(item)
        if group_id is None:
            return
        text = self.group_header_text(group_id, self.group_items.get(group_id, []), item.isExpanded())
        item.setText(0, text)
        for column in range(self.tree.columnCount()):
            item.setToolTip(column, text)
        self.style_duplicate_header(item, len(self.group_items.get(group_id, [])) < 2)

    def update_subgroup_header_item(self, item: Optional[QTreeWidgetItem]):
        if not item or item.data(0, self.ROLE_KIND) != "subgroup":
            return
        base = str(item.data(0, self.ROLE_SUBGROUP) or "").lstrip("▼▶ ").strip()
        marker = "▼" if item.isExpanded() else "▶"
        text = f"{marker} {base}"
        item.setText(0, text)
        for column in range(self.tree.columnCount()):
            item.setToolTip(column, text)
        self.style_duplicate_subheader(item, len(self.descendant_file_paths(item)) < 2)

    def update_duplicate_header_item(self, item: Optional[QTreeWidgetItem]):
        if not item:
            return
        if item.data(0, self.ROLE_KIND) == "group":
            self.update_group_header_item(item)
        elif item.data(0, self.ROLE_KIND) == "subgroup":
            self.update_subgroup_header_item(item)

    def toggle_duplicate_header(self, item: QTreeWidgetItem):
        kind = item.data(0, self.ROLE_KIND)
        if kind not in {"group", "subgroup"}:
            return
        expanded = not item.isExpanded()
        item.setExpanded(expanded)
        group_id = self.tree_item_group(item)
        if group_id is not None:
            if kind == "group":
                if expanded:
                    self.user_collapsed_group_ids.discard(group_id)
                else:
                    self.user_collapsed_group_ids.add(group_id)
            else:
                subgroup_text = str(item.data(0, self.ROLE_SUBGROUP) or "")
                subgroup_key = (group_id, subgroup_text)
                if expanded:
                    self.user_collapsed_subgroups.discard(subgroup_key)
                else:
                    self.user_collapsed_subgroups.add(subgroup_key)
        self.update_duplicate_header_item(item)

    def open_tree_item(self, item: QTreeWidgetItem, _column: int = 0):
        if item.data(0, self.ROLE_KIND) in {"group", "subgroup"}:
            return
        path = self.tree_item_path(item)
        if path:
            self.open_file(path)

    def open_current_item(self):
        item = self.tree.currentItem()
        if not item:
            return

        if item.data(0, self.ROLE_KIND) in {"group", "subgroup"}:
            return

        path = self.tree_item_path(item)
        if path:
            self.open_file(path)

    def meta_for_duplicate_path(self, path: Path) -> Optional[MediaMeta]:
        matches = self.dup_items_by_path.get(normalized_folder_path(path), [])
        if matches:
            dup = matches[0]
            return MediaMeta(
                duration=dup.duration,
                sample_rate=dup.sample_rate,
                resolution=dup.resolution,
                duration_seconds=dup.duration_seconds,
                sample_rate_hz=dup.sample_rate_hz,
                width=dup.width,
                height=dup.height,
            )
        return None

    def update_duplicate_preview(self):
        item = self.tree.currentItem()
        path = self.tree_item_path(item)
        if not path and item and item.data(0, self.ROLE_KIND) == "group":
            group_id = self.tree_item_group(item)
            group = self.group_items.get(group_id, []) if group_id is not None else []
            if group:
                path = group[0].file
        if not path and item and item.data(0, self.ROLE_KIND) == "subgroup":
            child = self.first_descendant_file_item(item)
            path = self.tree_item_path(child)

        if path:
            selection_changed = path != self.current_active_file_path
            if path != self.current_active_file_path:
                if self.current_active_file_path and self.current_active_file_path.exists():
                    self.previous_active_file_path = self.current_active_file_path
                self.current_active_file_path = path
            large_open = bool(self.quicklook_dialog and self.quicklook_dialog.isVisible())
            if selection_changed:
                debug_log(
                    "input",
                    "duplicate table row selected",
                    force=True,
                    row_kind=item.data(0, self.ROLE_KIND) if item else "none",
                    selected_rows=len(self.tree.selectedItems()),
                    media_kind=kind_for_path(path),
                    preview_window_open=large_open,
                )
            if large_open:
                self.duplicate_preview_timer.stop()
                self.pending_duplicate_preview_path = None
                self.quicklook_dialog.queue_path(path, self.meta_for_duplicate_path(path))
            else:
                self.schedule_duplicate_preview(path)
        else:
            self.duplicate_preview_timer.stop()
            self.pending_duplicate_preview_path = None
            self.preview_panel.reset()

    def schedule_duplicate_preview(self, path: Path):
        if getattr(self.preview_panel, "current_path", None) == path:
            self.duplicate_preview_timer.stop()
            self.pending_duplicate_preview_path = None
            return
        self.pending_duplicate_preview_path = path
        # Debounce rapid arrow-key traversal, but keep deliberate row changes
        # feeling immediate even while scan results are streaming into the tree.
        self.duplicate_preview_timer.start(180 if self.worker and self.worker.isRunning() else 95)

    def apply_pending_duplicate_preview(self):
        path = self.pending_duplicate_preview_path
        self.pending_duplicate_preview_path = None
        if not path or not path.exists():
            self.preview_panel.reset()
            return
        if self.quicklook_dialog and self.quicklook_dialog.isVisible():
            self.quicklook_dialog.queue_path(path, self.meta_for_duplicate_path(path))
            return
        if getattr(self.preview_panel, "current_path", None) == path:
            return
        self.preview_panel.set_path(
            path,
            self.meta_for_duplicate_path(path),
            # DuplicateWorker is already probing media and publishes its cache
            # into this panel.  Starting another ffprobe for a selected row while
            # the scan is active steals decoder/IO time from both playback and
            # the scan without adding information.
            probe_media=not self.scan_thread_running(),
        )

    def preview_current_item(self, toggle: bool = True):
        item = self.tree.currentItem()
        if not item:
            return
        path = self.tree_item_path(item)
        if not path and item.data(0, self.ROLE_KIND) in {"group", "subgroup"}:
            path = self.tree_item_path(self.first_descendant_file_item(item))
        if path:
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
                    "duplicate preview window closing from Space",
                    force=True,
                )
                self.quicklook_dialog.close()
                return
            self.zoom_duplicate_preview(path)

    def clear_duplicate_selection(self):
        self.current_active_file_path = None
        self.duplicate_preview_timer.stop()
        self.pending_duplicate_preview_path = None
        self.preview_panel.reset()
        if self.quicklook_dialog and self.quicklook_dialog.isVisible():
            self.quicklook_dialog.close()

    def open_adjacent_file(self, direction: int, video_only: bool = False) -> bool:
        items = self.file_items_in_order()
        if video_only:
            items = [
                item for item in items
                if (path := self.tree_item_path(item)) is not None and is_video_path(path)
            ]
        if not items:
            return False

        current = self.tree.currentItem()
        try:
            index = items.index(current)
        except ValueError:
            current_path = self.current_file_path()
            index = next((i for i, item in enumerate(items) if self.tree_item_path(item) == current_path), 0)

        next_index = index + direction
        if next_index < 0 or next_index >= len(items):
            return False
        target = items[next_index]
        self.tree.clearSelection()
        target.setSelected(True)
        self.tree.setCurrentItem(target)
        self.tree.scrollToItem(target)

        path = self.tree_item_path(target)
        if path:
            if self.quicklook_dialog and self.quicklook_dialog.isVisible():
                self.quicklook_dialog.queue_path(path, self.meta_for_duplicate_path(path))
            else:
                self.schedule_duplicate_preview(path)
            return True
        return False

    def open_context_menu(self, position):
        item = self.tree.itemAt(position)
        if not item:
            return

        menu = QMenu(self)
        if item.data(0, self.ROLE_KIND) in {"group", "subgroup"}:
            if not item.isSelected():
                self.tree.clearSelection()
                item.setSelected(True)
                self.tree.setCurrentItem(item)
            is_subgroup = item.data(0, self.ROLE_KIND) == "subgroup"
            preview_group = menu.addAction("Preview First File")
            reveal_group = menu.addAction("Reveal Match Set in Finder" if is_subgroup else "Reveal Group in Finder")
            menu.addSeparator()
            delete_group = menu.addAction("Move Match Set to Trash" if is_subgroup else "Move Group to Trash")
            chosen = menu.exec(self.tree.viewport().mapToGlobal(position))
            if chosen == preview_group:
                first_file = self.first_descendant_file_item(item)
                first_path = self.tree_item_path(first_file)
                if first_path:
                    self.zoom_duplicate_preview(first_path)
            elif chosen == reveal_group:
                if is_subgroup:
                    self.stage_paths_for_review(self.descendant_file_paths(item), "Match Set")
                else:
                    group_id = self.tree_item_group(item)
                    if group_id is not None:
                        self.stage_group_for_review(group_id)
            elif chosen == delete_group:
                if is_subgroup:
                    self.move_selected_to_trash(self.descendant_file_paths(item))
                else:
                    group_id = self.tree_item_group(item)
                    self.move_selected_to_trash(self.paths_for_group(group_id) if group_id is not None else [])
            return

        path = self.tree_item_path(item)
        if not path:
            return
        if not item.isSelected():
            self.tree.clearSelection()
            item.setSelected(True)
            self.tree.setCurrentItem(item)

        selected_paths = self.selected_paths()
        selected_count = len(selected_paths)

        open_action = menu.addAction("Open")
        preview_action = menu.addAction("Preview")
        reveal_action = menu.addAction("Reveal in Finder")
        menu.addSeparator()
        delete_action = menu.addAction("Move Selected to Trash" if selected_count > 1 else "Move to Trash")
        chosen = menu.exec(self.tree.viewport().mapToGlobal(position))

        if chosen == open_action:
            self.open_file(path)
        elif chosen == preview_action:
            self.preview_current_item(toggle=False)
        elif chosen == reveal_action:
            self.reveal_file(path)
        elif chosen == delete_action:
            self.move_selected_to_trash()

    def paths_for_group(self, group_id: int) -> List[Path]:
        paths = []
        for item in self.group_items.get(group_id, []):
            if item.file.exists():
                paths.append(item.file)
        return paths

    def stage_group_for_review(self, group_id: int):
        paths = self.paths_for_group(group_id)
        self.stage_paths_for_review(paths, f"Group {group_id:02d}")

    def stage_paths_for_review(self, paths: List[Path], label: str):
        self.restore_active_review()

        if not paths:
            QMessageBox.information(self, "No files", "There are no available files in this set.")
            return

        video_paths = [path for path in paths if is_video_path(path)]
        stage_paths = video_paths or paths
        safe_label = re.sub(r"[^A-Za-z0-9._ -]+", "", label).strip() or "Review"
        target_folder = unique_path(self.folder / f"Folder Manager Duplicate Review - {safe_label}")
        target_folder.mkdir(parents=True, exist_ok=True)

        moves: List[ReviewMove] = []
        for source in stage_paths:
            target = unique_path(target_folder / source.name)
            try:
                shutil.move(str(source), str(target))
                moves.append(ReviewMove(original=source, staged=target))
                self.replace_path_references(source, target)
            except OSError:
                continue

        if not moves:
            QMessageBox.warning(self, "Could not stage files", "No files could be placed in the review folder.")
            try:
                target_folder.rmdir()
            except OSError:
                pass
            return

        self.active_review_folder = target_folder
        self.active_review_moves = moves
        subprocess.Popen(
            ["open", str(target_folder)],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        self.review_watcher = FinderWindowWatcher(target_folder)
        self.review_watcher.closed.connect(self.restore_review_from_signal)
        self.review_watcher.start()
        self.progress_label.setText(f"Reviewing {label}; close Finder window to restore files")

    def replace_path_references(self, old: Path, new: Path):
        affected_groups: set[int] = set()
        for dup in self.all_dup_items:
            if dup.file == old:
                dup.file = new
                affected_groups.add(dup.group)
        for group in self.group_items.values():
            for dup in group:
                if dup.file == old:
                    dup.file = new
                    affected_groups.add(dup.group)

        old_key = normalized_folder_path(old)
        new_key = normalized_folder_path(new)
        moved_items = self.dup_items_by_path.pop(old_key, [])
        if moved_items:
            existing_ids = {id(item) for item in self.dup_items_by_path.get(new_key, [])}
            self.dup_items_by_path[new_key].extend(item for item in moved_items if id(item) not in existing_ids)
        old_meta = self.live_metadata_cache.pop(old, None)
        if old_meta is not None:
            self.live_metadata_cache[new] = old_meta
        for group_id in affected_groups:
            group = self.group_items.get(group_id, [])
            if group:
                self.group_fingerprints[group_id] = self.duplicate_group_fingerprint(group)

        def update_children(parent: QTreeWidgetItem):
            for child_index in range(parent.childCount()):
                child = parent.child(child_index)
                if self.tree_item_path(child) == old:
                    child.setData(0, self.ROLE_PATH, str(new))
                    child.setToolTip(0, str(new))
                update_children(child)

        for top_index in range(self.tree.topLevelItemCount()):
            update_children(self.tree.topLevelItem(top_index))

    def restore_review_from_signal(self, _folder_text: str):
        self.restore_active_review()

    def restore_active_review(self):
        if self.review_watcher and self.review_watcher.isRunning():
            self.review_watcher.stop()
            self.review_watcher.wait()
        self.review_watcher = None

        if not self.active_review_moves and not self.active_review_folder:
            return

        for move in list(self.active_review_moves):
            if not move.staged.exists():
                continue
            target = move.original
            try:
                target.parent.mkdir(parents=True, exist_ok=True)
                restored = unique_path(target) if target.exists() else target
                shutil.move(str(move.staged), str(restored))
                self.replace_path_references(move.staged, restored)
            except OSError:
                pass

        if self.active_review_folder:
            try:
                self.active_review_folder.rmdir()
            except OSError:
                pass

        self.active_review_folder = None
        self.active_review_moves = []
        self.progress_label.setText("Review folder restored")
        owner = self.owner_window
        if owner and hasattr(owner, "reload_folder"):
            owner.reload_folder("Review folder restored")

    def open_file(self, path: Path):
        if path.exists():
            open_file_reusing_finder(path)
            self.tree.setFocus(Qt.OtherFocusReason)
        else:
            QMessageBox.warning(self, "Missing file", "That file no longer exists.")

    def zoom_duplicate_preview(self, path: Path):
        if not path.exists():
            QMessageBox.warning(self, "Missing file", "That file no longer exists.")
            return
        self.set_preview_navigation_active(True)
        created = self.quicklook_dialog is None
        if created:
            self.quicklook_dialog = LargePreviewDialog(
                self,
                self.open_adjacent_file,
                self.move_selected_to_trash,
                self.meta_for_duplicate_path,
                self.current_file_path,
                embedded_preview_panel=self.preview_panel,
            )
        self.quicklook_dialog.set_path(path, self.meta_for_duplicate_path(path))
        self.quicklook_dialog.show()
        self.quicklook_dialog.raise_()
        self.quicklook_dialog.activateWindow()
        self.preview_panel.pause_video_preview()
        debug_log(
            "response",
            "separate preview window opened",
            force=True,
            context="duplicate scan",
            created=created,
            media_kind=kind_for_path(path),
            width=self.quicklook_dialog.width(),
            height=self.quicklook_dialog.height(),
        )

    def set_preview_navigation_active(self, active: bool):
        self.preview_navigation_active = active
        self.tree.preview_navigation_active = active

    def reveal_file(self, path: Path):
        if path.exists():
            reveal_in_finder(path)
        else:
            QMessageBox.warning(self, "Missing file", "That file no longer exists.")

    def remember_deleted_duplicates(self, paths: List[Path]) -> set[int]:
        path_set = set(paths)
        affected_groups: set[int] = set()
        for dup in list(self.all_dup_items):
            if dup.file in path_set:
                affected_groups.add(dup.group)
                self.deleted_dup_items_by_path[dup.file].append(dup)
        return affected_groups

    def remember_cleaned_groups(self, affected_groups: Iterable[int]):
        for group_id in affected_groups:
            remaining = [
                dup for dup in self.group_items.get(group_id, [])
                if dup.file.exists() and dup.file not in self.suppressed_paths
            ]
            if remaining and len(remaining) < 2:
                self.cleaned_group_items[group_id] = remaining
            elif len(remaining) >= 2:
                self.cleaned_group_items.pop(group_id, None)

    def move_selected_to_trash(self, paths_override: Optional[List[Path]] = None):
        paths = paths_override if paths_override is not None else self.selected_paths()
        paths = list(dict.fromkeys(paths))
        if not paths:
            return
        safety_message = duplicate_deletion_safety_message(self.group_items.values(), paths)
        if safety_message:
            QMessageBox.warning(self, "Deletion blocked", safety_message)
            return
        before_paths = self.file_paths_in_order()
        current_path = self.current_file_path()
        anchor_path = current_path if current_path in paths else paths[0]
        try:
            anchor_index = before_paths.index(anchor_path)
        except ValueError:
            anchor_index = 0
        selected_indexes = [before_paths.index(path) for path in paths if path in before_paths]
        if selected_indexes:
            first_selected_index = min(selected_indexes)
            fallback_index = max(0, first_selected_index - 1)
        else:
            fallback_index = anchor_index

        preferred_path = None
        for candidate in reversed(before_paths[: min(selected_indexes) if selected_indexes else 0]):
            if candidate and candidate.exists() and candidate not in paths:
                preferred_path = candidate
                break
        affected_groups = self.remember_deleted_duplicates(paths)
        worker = self.worker
        if worker is not None:
            try:
                if worker.isRunning():
                    worker.allow_paths_removed(paths)
            except RuntimeError:
                pass
        self.suppressed_paths.update(paths)
        self.remove_duplicate_paths_from_model(paths)
        self.remember_cleaned_groups(affected_groups)
        self.remove_duplicate_paths_from_tree(paths)
        self.select_file_after_refresh(select_path=preferred_path, select_index=fallback_index)
        self.set_preview_navigation_active(True)
        self.start_background_trash_move(paths)

    def remove_duplicate_paths_from_model(self, paths: List[Path]):
        path_set = set(paths)
        self.all_dup_items = [dup for dup in self.all_dup_items if dup.file not in path_set]
        for group_id in list(self.group_items):
            remaining = [dup for dup in self.group_items[group_id] if dup.file not in path_set]
            if remaining:
                self.group_items[group_id] = remaining
            else:
                del self.group_items[group_id]
                self.group_header_items.pop(group_id, None)
        self.group_fingerprints = {
            group_id: self.duplicate_group_fingerprint(group)
            for group_id, group in self.group_items.items()
        }
        self.rebuild_duplicate_path_index()

    def remove_duplicate_paths_from_tree(self, paths: List[Path]):
        path_set = set(paths)
        if not path_set:
            return

        def prune(parent: QTreeWidgetItem) -> bool:
            for child_index in range(parent.childCount() - 1, -1, -1):
                child = parent.child(child_index)
                child_path = self.tree_item_path(child)
                if child_path in path_set:
                    parent.takeChild(child_index)
                    continue
                if child_path is None and not prune(child):
                    parent.takeChild(child_index)
            return bool(self.descendant_file_items(parent))

        previous_block = self.tree.blockSignals(True)
        previous_updates = self.tree.updatesEnabled()
        self.tree.setUpdatesEnabled(False)
        try:
            for top_index in range(self.tree.topLevelItemCount() - 1, -1, -1):
                top = self.tree.topLevelItem(top_index)
                if not prune(top):
                    self.tree.takeTopLevelItem(top_index)
                    continue
                for child_index in range(top.childCount()):
                    child = top.child(child_index)
                    if child.data(0, self.ROLE_KIND) == "subgroup":
                        self.update_subgroup_header_item(child)
                        self.style_duplicate_subheader(child, len(self.descendant_file_items(child)) < 2)
                        for file_item in self.descendant_file_items(child):
                            if len(self.descendant_file_items(child)) < 2:
                                self.style_cleaned_duplicate_item(file_item)
                self.update_group_header_item(top)
                top_cleaned = len(self.descendant_file_items(top)) < 2
                self.style_duplicate_header(top, top_cleaned)
                for file_item in self.descendant_file_items(top):
                    if top_cleaned:
                        self.style_cleaned_duplicate_item(file_item)
        finally:
            self.tree.blockSignals(previous_block)
            self.tree.setUpdatesEnabled(previous_updates)
            self.tree.viewport().update()

    def on_background_trash_finished(self, worker: TrashMoveWorker, moves: List[TrashMove], failures: List[Path]):
        normalized_moves: List[TrashMove] = []
        for move in moves:
            original = self.original_path_for_active_review_path(move.original)
            if original is not None:
                staged = move.original
                move.original = original
                staged_items = self.deleted_dup_items_by_path.pop(staged, [])
                if staged_items:
                    original_items = self.deleted_dup_items_by_path[original]
                    original_ids = {id(item) for item in original_items}
                    for item in staged_items:
                        item.file = original
                        if id(item) not in original_ids:
                            original_items.append(item)
                self.suppressed_paths.discard(staged)
                self.suppressed_paths.add(original)
                self.replace_path_references(staged, original)
            normalized_moves.append(move)
        if normalized_moves:
            self.undo_stack.append(TrashAction(normalized_moves))
            self.redo_stack.clear()
            self.update_undo_button()
        if failures:
            restored_groups: set[int] = set()
            existing_keys = {(dup.group, normalized_folder_path(dup.file)) for dup in self.all_dup_items}
            for path in failures:
                self.suppressed_paths.discard(path)
                for dup in self.deleted_dup_items_by_path.pop(path, []):
                    dup.file = path
                    restored_groups.add(dup.group)
                    key = (dup.group, normalized_folder_path(path))
                    if key not in existing_keys:
                        self.all_dup_items.append(dup)
                        existing_keys.add(key)
            for group_id in restored_groups:
                self.cleaned_group_items.pop(group_id, None)
            self.progress_label.setText(
                f"Moved {human_count(len(normalized_moves))}; {human_count(len(failures))} failed"
            )
            self.refresh_tree_from_items()
        else:
            self.progress_label.setText(f"Moved {human_count(len(normalized_moves))} file(s) to Trash")
        self.reload_owner("Moved file(s) to Trash")

    def original_path_for_active_review_path(self, path: Path) -> Optional[Path]:
        for move in self.active_review_moves:
            if move.staged == path:
                return move.original
        return None

    def undo_trash(self):
        if not self.undo_stack:
            return

        action = self.undo_stack.pop()
        restored_moves: List[TrashMove] = []
        remaining_moves: List[TrashMove] = []
        restored_items: List[DupItem] = []
        for move in action.moves:
            source = move.trash
            if not source or not source.exists():
                remaining_moves.append(move)
                continue
            target = unique_path(move.original) if move.original.exists() else move.original
            try:
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.move(str(source), str(target))
                move.restored = target
                for dup in self.deleted_dup_items_by_path.pop(move.original, []):
                    dup.file = target
                    restored_items.append(dup)
                self.suppressed_paths.discard(move.original)
                self.suppressed_paths.discard(target)
                restored_moves.append(move)
            except OSError:
                remaining_moves.append(move)

        if restored_moves:
            existing_keys = {(dup.group, normalized_folder_path(dup.file)) for dup in self.all_dup_items}
            for dup in restored_items:
                key = (dup.group, normalized_folder_path(dup.file))
                if key not in existing_keys:
                    self.all_dup_items.append(dup)
                    existing_keys.add(key)
            for group_id in {dup.group for dup in restored_items}:
                self.cleaned_group_items.pop(group_id, None)
            self.redo_stack.append(TrashAction(restored_moves))
            first_move = restored_moves[0]
            self.refresh_tree_from_items(select_path=first_move.restored or first_move.original)
            self.progress_label.setText(f"Restored {human_count(len(restored_moves))} file(s)")
            self.reload_owner("Restored file(s)")
        if remaining_moves:
            self.undo_stack.append(TrashAction(remaining_moves))
        self.update_undo_button()

    def redo_trash(self):
        if not self.redo_stack:
            return

        action = self.redo_stack.pop()
        moved_moves: List[TrashMove] = []
        remaining_moves: List[TrashMove] = []
        for move in action.moves:
            source = move.restored or move.original
            if not source.exists():
                remaining_moves.append(move)
                continue
            new_move = move_to_trash_recorded(source)
            if new_move:
                move.trash = new_move.trash
                move.restored = None
                moved_moves.append(move)
            else:
                remaining_moves.append(move)

        if moved_moves:
            self.undo_stack.append(TrashAction(moved_moves))
            self.update_undo_button()
            self.refresh_tree_from_items()
            self.progress_label.setText(f"Moved {human_count(len(moved_moves))} file(s) back to Trash")
            self.reload_owner("Moved file(s) to Trash")
        if remaining_moves:
            self.redo_stack.append(TrashAction(remaining_moves))
        self.update_undo_button()

    def reload_owner(self, status: str):
        owner = self.owner_window
        if owner and hasattr(owner, "reload_folder"):
            owner.reload_folder(status)

    def resizeEvent(self, event):
        super().resizeEvent(event)
        schedule_settled_window_geometry_remember(self)

    def moveEvent(self, event):
        super().moveEvent(event)
        schedule_settled_window_geometry_remember(self)

    def showEvent(self, event):
        super().showEvent(event)
        temporarily_attach_window_to_owner_space(self, self.owner_window)
        schedule_macos_native_fullscreen_button(self)

    def changeEvent(self, event):
        track_standard_fullscreen_change(self, event, "duplicate_scan")
        if promote_macos_zoom_to_fullscreen(
            self,
            event,
            before_promote=lambda: capture_standard_window_geometry(self, "duplicate_scan"),
        ):
            event.accept()
            return
        super().changeEvent(event)

    def closeEvent(self, event):
        debug_window_close_context(self, "scanner")
        if self.scan_thread_running() or self.trash_thread_running():
            self.close_after_scan_stops = True
            if self.worker and self.worker.isRunning():
                self.stop_scan()
            self.stop_background_trash_moves()
            self.progress_label.setText("Finishing active file work before closing")
            event.ignore()
            return
        if defer_close_until_windowed(self, event, "duplicate_scan"):
            return
        save_window_geometry(self, "duplicate_scan")
        save_tree_header_state(self.tree, "duplicate_v3")
        self.restore_active_review()
        if self.quicklook_dialog and self.quicklook_dialog.isVisible():
            self.quicklook_dialog.close()
        self.preview_panel.stop_preview_workers()
        super().closeEvent(event)


# ---------------------------------------------------------------------------
# File integrity validation


@dataclass
class BadFileItem:
    file: Path
    kind: str
    issue: str
    details: str = ""
    duration: str = ""
    frame_rate: str = ""
    sample_rate: str = ""
    resolution: str = ""
    bit_rate: str = ""
    codec: str = ""


@dataclass
class MediaTimelineCheck:
    healthy: Optional[bool]
    last_timestamp: float = 0.0
    details: str = ""


@dataclass
class MediaSampleCheck:
    healthy: Optional[bool]
    details: str = ""


def _ffmpeg_progress_seconds(output: str) -> float:
    last_timestamp = 0.0
    for line in (output or "").splitlines():
        if not line.startswith("out_time="):
            continue
        value = line.partition("=")[2].strip()
        try:
            hours, minutes, seconds = value.split(":", 2)
            last_timestamp = max(
                last_timestamp,
                (float(hours) * 3600.0) + (float(minutes) * 60.0) + float(seconds),
            )
        except (TypeError, ValueError):
            continue
    return last_timestamp


def _ffmpeg_validation_is_inconclusive(output: str) -> bool:
    """Separate an unavailable decoder/DRM stream from proven file damage."""
    text = (output or "").casefold()
    markers = (
        "decoder not found",
        "unknown decoder",
        "no decoder found",
        "unsupported codec",
        "codec is not supported",
        "not implemented for",
        "operation not permitted",  # Common for protected/DRM media.
        "encrypted",
        "decryption key",
    )
    return any(marker in text for marker in markers)


def human_media_validation_error(
    output: str,
    *,
    video: bool,
    last_timestamp: float = 0.0,
) -> str:
    """Translate decoder diagnostics into a useful explanation for a person."""
    text = (output or "").casefold()
    position = format_duration(last_timestamp) if last_timestamp > 0 else ""
    where = f" around {position}" if position else ""

    if "moov atom not found" in text:
        return (
            "The MP4/MOV index is missing, so the file cannot be opened. "
            "It is probably incomplete or was never finalized when it was created."
        )
    if any(marker in text for marker in ("partial file", "end of file", "truncated")):
        return (
            f"The file ends unexpectedly{where}. Part of the media is missing, "
            "so playback may stop before the end."
        )
    if any(
        marker in text
        for marker in (
            "invalid nal",
            "corrupt decoded frame",
            "error while decoding",
            "decode_slice_header",
            "missing reference picture",
            "error splitting the input",
        )
    ):
        media_part = "video frame" if video else "audio data"
        return (
            f"At least one {media_part}{where} is damaged and could not be decoded "
            "reliably. Playback may stop, glitch, or lose sound at that point."
        )
    if "invalid data found when processing input" in text:
        if position:
            return (
                f"Decoding stopped around {position} because the remaining media data "
                "is invalid or incomplete."
            )
        return (
            "The media container cannot be opened. Its contents are incomplete, "
            "damaged, or do not match the filename extension."
        )
    if any(marker in text for marker in ("permission denied", "input/output error")):
        return (
            "Folder Manager lost access while reading this file. Check its permissions "
            "and make sure the disk is still connected and working."
        )
    media_part = "video and audio" if video else "audio"
    return (
        f"FFmpeg stopped while decoding the {media_part}{where}. The stream contains "
        "data that a normal decoder could not read."
    )


def _media_validation_timeout(path: Path, duration: float) -> float:
    try:
        size_gib = path.stat().st_size / float(1024 ** 3)
    except OSError:
        size_gib = 0.0
    # Complete decoding is intentionally more expensive than sampling. Give
    # long/high-resolution files enough time to finish even when several jobs
    # share an external disk. A timeout remains inconclusive, never "bad".
    return min(1800.0, max(60.0, 30.0 + (size_gib * 120.0) + (duration * 0.15)))


def ffmpeg_validate_media_timeline(path: Path, duration: float, video: bool) -> MediaTimelineCheck:
    """Decode every audio/video frame; sampling alone can miss real corruption."""
    ffmpeg = ffmpeg_path()
    if ffmpeg is None:
        return MediaTimelineCheck(None)

    command = [
        ffmpeg,
        "-hide_banner",
        "-nostdin",
        "-v",
        "error",
        "-xerror",
        "-err_detect",
        "explode",
        "-threads",
        "2",
    ]
    command.extend(
        [
            "-i",
            str(path),
            # Validate every audio/video stream in the container, not merely the
            # first stream implied by the filename extension.
            "-map",
            "0:v?",
            "-map",
            "0:a?",
            "-sn",
            "-dn",
            "-progress",
            "pipe:1",
            "-nostats",
            "-f",
            "null",
            "-",
        ]
    )

    try:
        with ScanMediaSlot():
            result = scan_subprocess_run(
                command,
                text=True,
                capture_output=True,
                timeout=_media_validation_timeout(path, duration),
            )
    except subprocess.TimeoutExpired:
        return MediaTimelineCheck(None, details="Full timeline validation timed out.")
    except ScanCancelled:
        raise
    except Exception as exc:
        return MediaTimelineCheck(None, details=f"{type(exc).__name__}: {exc}")

    last_timestamp = _ffmpeg_progress_seconds(result.stdout)
    error_text = (result.stderr or "").strip()
    if _ffmpeg_validation_is_inconclusive(error_text):
        return MediaTimelineCheck(
            None,
            last_timestamp,
            "This media uses a protected or unsupported format, so it could not be checked reliably.",
        )
    if result.returncode != 0 or error_text:
        return MediaTimelineCheck(
            False,
            last_timestamp,
            human_media_validation_error(
                error_text,
                video=video,
                last_timestamp=last_timestamp,
            ),
        )
    if not last_timestamp and duration > 1.0:
        return MediaTimelineCheck(None, details="The stream produced no timeline progress.")
    if duration > 5.0:
        allowed_gap = max(2.0, min(30.0, duration * 0.02))
        if last_timestamp + allowed_gap < duration:
            return MediaTimelineCheck(
                False,
                last_timestamp,
                "The file claims to last "
                f"{format_duration(duration)}, but complete decoding stopped at "
                f"{format_duration(last_timestamp)}. The missing ending is likely truncated.",
            )
    # A successful complete audio/video decode has already traversed the media
    # that determines playback. The former second full-file stream-copy pass
    # doubled scan I/O and made large-library ETA/speed needlessly poor.
    return MediaTimelineCheck(True, last_timestamp)


def media_sample_timestamps(duration: float) -> List[float]:
    """Return de-duplicated positions covering the complete declared timeline."""
    if duration <= 0:
        return [0.0]
    if duration <= 4.0:
        return [0.0]
    positions = [
        0.3,
        duration * 0.08,
        duration * 0.20,
        duration * 0.34,
        duration * 0.49,
        duration * 0.64,
        duration * 0.78,
        duration * 0.90,
        max(0.3, duration - 2.0),
    ]
    unique: List[float] = []
    for position in positions:
        position = max(0.0, min(position, max(0.0, duration - 0.2)))
        if not any(abs(position - existing) < 0.35 for existing in unique):
            unique.append(position)
    return unique


def ffmpeg_validate_media_samples(path: Path, duration: float, video: bool) -> MediaSampleCheck:
    """Decode media at distributed positions in one FFmpeg process.

    Multiple seekable inputs provide broad timeline coverage without rereading
    the complete file or paying process startup once per sample.
    """
    ffmpeg = ffmpeg_path()
    if ffmpeg is None:
        return MediaSampleCheck(None)

    positions = media_sample_timestamps(duration)
    command = [
        ffmpeg,
        "-hide_banner",
        "-nostdin",
        "-v",
        "error",
        "-xerror",
        "-err_detect",
        "explode",
        "-threads",
        "2",
    ]
    for position in positions:
        command.extend(["-ss", f"{position:.3f}", "-t", "0.90", "-i", str(path)])
    for input_index in range(len(positions)):
        command.extend(
            [
                "-map",
                f"{input_index}:{'v' if video else 'a'}:0",
                "-an" if video else "-vn",
                "-f",
                "null",
                "-",
            ]
        )

    try:
        with ScanMediaSlot():
            result = scan_subprocess_run(
                command,
                text=True,
                capture_output=True,
                timeout=min(90.0, max(25.0, 14.0 + len(positions) * 4.0)),
            )
    except subprocess.TimeoutExpired:
        return MediaSampleCheck(None, "Distributed frame validation timed out.")
    except ScanCancelled:
        raise
    except Exception as exc:
        return MediaSampleCheck(None, f"{type(exc).__name__}: {exc}")

    error_text = (result.stderr or result.stdout or "").strip()
    if _ffmpeg_validation_is_inconclusive(error_text):
        return MediaSampleCheck(
            None,
            "This media uses a protected or unsupported format, so it could not be checked reliably.",
        )
    if result.returncode == 0 and not error_text:
        return MediaSampleCheck(True)

    failed_positions: List[str] = []
    for match in re.finditer(r"(?:ist|ost)#(\d+):", error_text):
        input_index = int(match.group(1))
        if input_index < len(positions):
            label = format_duration(positions[input_index])
            if label not in failed_positions:
                failed_positions.append(label)
    sample_timestamp = positions[0] if len(failed_positions) == 1 else 0.0
    return MediaSampleCheck(
        False,
        human_media_validation_error(
            error_text,
            video=video,
            last_timestamp=sample_timestamp,
        ),
    )


OFFICE_ZIP_REQUIRED_MEMBERS = {
    ".docx": ("[Content_Types].xml", "word/document.xml"),
    ".xlsx": ("[Content_Types].xml", "xl/workbook.xml"),
    ".pptx": ("[Content_Types].xml", "ppt/presentation.xml"),
}
ZIP_DOCUMENT_REQUIRED_MEMBERS = {
    **OFFICE_ZIP_REQUIRED_MEMBERS,
    ".odt": ("mimetype", "content.xml"),
    ".ods": ("mimetype", "content.xml"),
    ".odp": ("mimetype", "content.xml"),
    ".epub": ("mimetype", "META-INF/container.xml"),
}
OLE_COMPOUND_FILE_MAGIC = b"\xd0\xcf\x11\xe0\xa1\xb1\x1a\xe1"


def validate_zip_container(path: Path, suffix: str) -> Tuple[Optional[bool], str]:
    """Validate readable ZIP members and the minimum Office package structure."""
    try:
        with zipfile.ZipFile(path) as archive:
            names = set(archive.namelist())
            missing = [
                member
                for member in ZIP_DOCUMENT_REQUIRED_MEMBERS.get(suffix, ())
                if member not in names
            ]
            if missing:
                document_name = {
                    ".docx": "Word document",
                    ".xlsx": "Excel workbook",
                    ".pptx": "PowerPoint presentation",
                    ".odt": "OpenDocument text document",
                    ".ods": "OpenDocument spreadsheet",
                    ".odp": "OpenDocument presentation",
                    ".epub": "EPUB book",
                }.get(suffix, "Office document")
                return (
                    False,
                    f"This is not a complete {document_name}. It is missing its required "
                    f"internal file: {missing[0]}.",
                )
            encrypted_members = 0
            for member in archive.infolist():
                raise_if_scan_cancelled()
                if member.is_dir():
                    continue
                if member.flag_bits & 0x1:
                    encrypted_members += 1
                    continue
                try:
                    with archive.open(member) as source:
                        while True:
                            raise_if_scan_cancelled()
                            if not source.read(1024 * 1024):
                                break
                except (zipfile.BadZipFile, EOFError, OSError):
                    return (
                        False,
                        f"The archive's internal file '{member.filename}' failed its "
                        "integrity check. The archive is incomplete or damaged.",
                    )
            if encrypted_members:
                return (
                    None,
                    f"{human_count(encrypted_members)} encrypted internal file(s) could not be "
                    "decompressed without the archive password. This is not proof of damage.",
                )
            for required_member in ZIP_DOCUMENT_REQUIRED_MEMBERS.get(suffix, ()):
                if not required_member.casefold().endswith(".xml"):
                    continue
                raise_if_scan_cancelled()
                try:
                    with archive.open(required_member) as source:
                        ET.parse(source)
                except ET.ParseError:
                    return (
                        False,
                        f"The document's required internal file '{required_member}' contains "
                        "incomplete or malformed XML.",
                    )

            expected_mimetypes = {
                ".odt": b"application/vnd.oasis.opendocument.text",
                ".ods": b"application/vnd.oasis.opendocument.spreadsheet",
                ".odp": b"application/vnd.oasis.opendocument.presentation",
                ".epub": b"application/epub+zip",
            }
            expected_mimetype = expected_mimetypes.get(suffix)
            if expected_mimetype is not None:
                with archive.open("mimetype") as source:
                    actual_mimetype = source.read(256).strip()
                if actual_mimetype != expected_mimetype:
                    return (
                        False,
                        "The document's internal media type does not match its filename extension.",
                    )
        return True, ""
    except zipfile.BadZipFile:
        return False, "The archive directory is missing or damaged, so its contents cannot be opened."
    except (PermissionError, RuntimeError):
        return (
            None,
            "The archive is encrypted or became inaccessible during its integrity check. "
            "This is not proof of damage, but its contents were not fully verified.",
        )
    except OSError as exc:
        return False, f"The archive could not be read from disk. macOS reported: {exc}."


def validate_tar_container(path: Path) -> Tuple[Optional[bool], str]:
    """Read every regular member of a TAR (including compressed TAR variants)."""
    try:
        with tarfile.open(path, mode="r:*") as archive:
            for member in archive:
                raise_if_scan_cancelled()
                if not member.isfile():
                    continue
                source = archive.extractfile(member)
                if source is None:
                    return False, f"The archive member '{member.name}' could not be opened."
                with source:
                    while True:
                        raise_if_scan_cancelled()
                        if not source.read(1024 * 1024):
                            break
        if path.suffix.lower() == ".tar":
            return (
                None,
                "Every TAR member was readable, but plain TAR files do not store checksums for "
                "member contents, so silent payload changes cannot be ruled out. This is not "
                "proof of damage.",
            )
        return True, ""
    except (tarfile.TarError, EOFError, OSError) as exc:
        return (
            False,
            "The TAR archive ended early or contains a damaged member, so all of its "
            f"contents could not be read ({type(exc).__name__}).",
        )


def validate_single_stream_archive(path: Path, suffix: str) -> Tuple[Optional[bool], str]:
    """Decompress a complete gzip/bzip2/xz stream so trailer checks are exercised."""
    opener = {".gz": gzip.open, ".bz2": bz2.open, ".xz": lzma.open}.get(suffix)
    if opener is None:
        return None, "No built-in integrity checker is available for this compression format."
    try:
        with opener(path, "rb") as source:
            while True:
                raise_if_scan_cancelled()
                if not source.read(1024 * 1024):
                    break
        return True, ""
    except (EOFError, OSError, lzma.LZMAError) as exc:
        return (
            False,
            "The compressed stream failed while being decompressed. It is incomplete or "
            f"damaged ({type(exc).__name__}).",
        )


def validate_legacy_office_container(head: bytes, suffix: str) -> Tuple[Optional[bool], str]:
    """Reject mislabeled legacy Office files; full OLE object validation is unavailable."""
    if not head.startswith(OLE_COMPOUND_FILE_MAGIC):
        return (
            False,
            f"The file has a {suffix} extension, but it does not contain a legacy Microsoft "
            "Office document header.",
        )
    return (
        None,
        "The legacy Office container header is readable, but its internal objects cannot be "
        "fully verified by this build. This is not proof of damage.",
    )


def _read_midi_variable_length(data: bytes, offset: int) -> Tuple[int, int]:
    value = 0
    for _index in range(4):
        if offset >= len(data):
            raise ValueError("truncated variable-length value")
        byte = data[offset]
        offset += 1
        value = (value << 7) | (byte & 0x7F)
        if byte < 0x80:
            return value, offset
    raise ValueError("invalid variable-length value")


def _validate_midi_track(data: bytes) -> None:
    offset = 0
    running_status: Optional[int] = None
    end_of_track = False
    while offset < len(data):
        _delta, offset = _read_midi_variable_length(data, offset)
        if offset >= len(data):
            raise ValueError("track ends before its event")
        status = data[offset]
        if status < 0x80:
            if running_status is None:
                raise ValueError("event data has no running status")
            status = running_status
        else:
            offset += 1

        if 0x80 <= status <= 0xEF:
            running_status = status
            data_length = 1 if (status & 0xF0) in {0xC0, 0xD0} else 2
            if offset + data_length > len(data):
                raise ValueError("channel event is truncated")
            if any(value >= 0x80 for value in data[offset : offset + data_length]):
                raise ValueError("channel event contains invalid data bytes")
            offset += data_length
            continue

        if status == 0xFF:
            running_status = None
            if offset >= len(data):
                raise ValueError("meta event has no type")
            meta_type = data[offset]
            offset += 1
            length, offset = _read_midi_variable_length(data, offset)
            if offset + length > len(data):
                raise ValueError("meta event is truncated")
            offset += length
            if meta_type == 0x2F:
                if length != 0:
                    raise ValueError("end-of-track event has data")
                end_of_track = True
                break
            continue

        if status in {0xF0, 0xF7}:
            running_status = None
            length, offset = _read_midi_variable_length(data, offset)
            if offset + length > len(data):
                raise ValueError("system-exclusive event is truncated")
            offset += length
            continue

        system_lengths = {0xF1: 1, 0xF2: 2, 0xF3: 1, 0xF6: 0}
        if status in system_lengths:
            running_status = None
            data_length = system_lengths[status]
            if offset + data_length > len(data):
                raise ValueError("system event is truncated")
            offset += data_length
            continue
        if 0xF8 <= status <= 0xFE:
            continue
        raise ValueError("unknown MIDI event")
    if not end_of_track:
        raise ValueError("track has no end-of-track event")


def validate_midi_file(path: Path) -> Tuple[Optional[bool], str]:
    """Parse every Standard MIDI track instead of sending non-audio events to FFmpeg."""
    try:
        file_size = path.stat().st_size
        with path.open("rb") as source:
            header = source.read(14)
            if len(header) != 14 or header[:4] != b"MThd":
                return False, "The file does not begin with a Standard MIDI header."
            header_length = int.from_bytes(header[4:8], "big")
            if header_length < 6:
                return False, "The MIDI header is incomplete."
            if header_length > 6:
                extra_header = source.read(header_length - 6)
                if len(extra_header) != header_length - 6:
                    return False, "The MIDI header ends unexpectedly."
            format_type = int.from_bytes(header[8:10], "big")
            track_count = int.from_bytes(header[10:12], "big")
            division = int.from_bytes(header[12:14], "big")
            if format_type > 2 or track_count <= 0 or division == 0:
                return False, "The MIDI header contains invalid format, track, or timing values."
            for track_index in range(track_count):
                raise_if_scan_cancelled()
                chunk_header = source.read(8)
                if len(chunk_header) != 8 or chunk_header[:4] != b"MTrk":
                    return False, f"MIDI track {track_index + 1} is missing its track header."
                track_length = int.from_bytes(chunk_header[4:8], "big")
                if track_length > file_size or track_length > 256 * 1024 * 1024:
                    return None, "A MIDI track is too large to verify safely in memory."
                track_data = source.read(track_length)
                if len(track_data) != track_length:
                    return False, f"MIDI track {track_index + 1} ends before its declared length."
                try:
                    _validate_midi_track(track_data)
                except ValueError as exc:
                    return False, f"MIDI track {track_index + 1} is damaged: {exc}."
            trailing = source.read(1)
            if trailing:
                return None, "The MIDI tracks are valid, but unexplained data follows the final track."
        return True, ""
    except OSError as exc:
        return False, f"The MIDI file could not be read from disk. macOS reported: {exc}."


def validate_image_contents(path: Path, suffix: str) -> Tuple[Optional[bool], str]:
    """Fully decode supported images without calling an unsupported format bad."""
    if suffix == ".svg":
        try:
            raise_if_scan_cancelled()
            document = ET.parse(path)
            tag = str(document.getroot().tag).rsplit("}", 1)[-1].casefold()
            if tag != "svg":
                return False, "The file has an .svg extension, but its contents are not an SVG image."
            return True, ""
        except ET.ParseError:
            return False, "The SVG markup is incomplete or malformed, so the image cannot be opened."
        except OSError as exc:
            return False, f"The image could not be read from disk. macOS reported: {exc}."

    try:
        from PIL import Image, UnidentifiedImageError
    except ImportError:
        return None, "The image decoder is not installed, so the image pixels were not checked."

    registered = {extension.casefold() for extension in Image.registered_extensions()}
    if suffix not in registered:
        return None, "The installed image decoder does not support this image format."
    try:
        with Image.open(path) as image:
            image.verify()
        # verify() checks the container; reopening and loading every frame also
        # detects truncated pixels in JPEGs and later frames in GIF/TIFF files.
        with Image.open(path) as image:
            frame_count = max(1, int(getattr(image, "n_frames", 1) or 1))
            for frame_index in range(frame_count):
                raise_if_scan_cancelled()
                image.seek(frame_index)
                image.load()
        return True, ""
    except Image.DecompressionBombError:
        # Pillow's safety limit says the image is very large, not that it is bad.
        return (
            None,
            "The image exceeds the decoder's safety size limit, so all pixels were not loaded. "
            "This is not proof of damage.",
        )
    except UnidentifiedImageError:
        return (
            False,
            "The file extension names an image format, but the contents are not a readable image.",
        )
    except (OSError, SyntaxError, ValueError, EOFError):
        return (
            False,
            "The image data is incomplete or damaged, so the whole image cannot be decoded.",
        )


def validate_pdf_structure(path: Path, head: bytes) -> Tuple[Optional[bool], str]:
    """Validate the PDF trailer, parser, and every renderable page."""
    if not head.startswith(b"%PDF"):
        return False, "The file has a .pdf extension, but its contents do not begin with a PDF document."
    try:
        size = path.stat().st_size
        with path.open("rb") as handle:
            handle.seek(max(0, size - 128 * 1024))
            tail = handle.read()
    except OSError as exc:
        return False, f"The PDF could not be read from disk. macOS reported: {exc}."
    if b"startxref" not in tail or b"%%EOF" not in tail:
        return (
            False,
            "The PDF is missing its closing index. It is probably incomplete or was cut off while saving or copying.",
        )
    try:
        from PySide6.QtPdf import QPdfDocument
    except ImportError:
        return (
            None,
            "The PDF header and closing index are present, but this build has no full PDF "
            "parser. This is not proof of damage.",
        )

    document = QPdfDocument()
    try:
        error = document.load(str(path))
        if error in {QPdfDocument.Error.IncorrectPassword, QPdfDocument.Error.UnsupportedSecurityScheme}:
            return (
                None,
                "The PDF is password-protected or uses an unsupported security scheme, so its "
                "pages could not be verified. This is not proof of damage.",
            )
        if error != QPdfDocument.Error.None_ or document.status() == QPdfDocument.Status.Error:
            return False, "The PDF parser could not load the document's object and page structure."
        page_count = int(document.pageCount())
        if page_count <= 0:
            return False, "The PDF contains no readable pages."
        for page_index in range(page_count):
            raise_if_scan_cancelled()
            image = document.render(page_index, QSize(48, 48))
            if image.isNull():
                return False, f"PDF page {page_index + 1} could not be decoded and rendered."
        return True, ""
    except ScanCancelled:
        raise
    except Exception as exc:
        return (
            None,
            "The PDF's basic structure is present, but its pages could not all be verified "
            f"({type(exc).__name__}). This is not proof of damage.",
        )
    finally:
        document.close()


def validate_sqlite_database(path: Path, head: bytes, suffix: str) -> Tuple[Optional[bool], str]:
    """Run SQLite's read-only quick_check without executing file contents."""
    magic = b"SQLite format 3\x00"
    if not head.startswith(magic):
        if suffix == ".sqlite":
            return False, "The file has a .sqlite extension, but it has no SQLite database header."
        return (
            None,
            "This .db file is not an SQLite database, so Folder Manager has no safe built-in "
            "integrity checker for its database format.",
        )
    try:
        import sqlite3

        connection = sqlite3.connect(
            f"{path.resolve().as_uri()}?mode=ro&immutable=1",
            uri=True,
            timeout=2.0,
        )
        try:
            worker = getattr(SCAN_SUBPROCESS_CONTEXT, "worker", None)

            def cancelled() -> int:
                return int(
                    worker is not None
                    and (worker._cancel_requested or worker.isInterruptionRequested())
                )

            connection.set_progress_handler(cancelled, 1000)
            messages = [str(row[0]) for row in connection.execute("PRAGMA quick_check")]
        finally:
            connection.close()
        raise_if_scan_cancelled()
        if messages == ["ok"]:
            return True, ""
        explanation = "; ".join(messages[:3])
        return False, f"SQLite's integrity check reported damaged database pages: {explanation}."
    except ScanCancelled:
        raise
    except Exception as exc:
        raise_if_scan_cancelled()
        return False, f"SQLite could not read the database structure ({type(exc).__name__})."


def validate_complete_file_read(path: Path, expected_size: int) -> Tuple[bool, str]:
    """Read every byte of otherwise unstructured files to catch disk I/O failures."""
    bytes_read = 0
    try:
        with path.open("rb") as source:
            while True:
                raise_if_scan_cancelled()
                chunk = source.read(4 * 1024 * 1024)
                if not chunk:
                    break
                bytes_read += len(chunk)
    except OSError as exc:
        return False, f"The file could not be read completely. macOS reported: {exc}."
    if bytes_read != expected_size:
        return (
            False,
            f"The file size changed while it was being read ({human_size(expected_size)} expected, "
            f"{human_size(bytes_read)} received).",
        )
    return True, ""


def _inspect_bad_file_uncached(path: Path) -> Optional[BadFileItem]:
    raise_if_scan_cancelled()
    kind = kind_for_path(path)
    try:
        st = path.stat()
    except OSError as exc:
        return BadFileItem(
            path,
            kind,
            "Unreadable file",
            f"Folder Manager could not read this file's information. macOS reported: {exc}.",
        )

    if st.st_size == 0:
        if path.suffix.lower() not in EMPTY_FILE_IS_INVALID_EXTS:
            # Empty text, source-code, log, CSV, and extensionless files are
            # perfectly legitimate. Only formats that require a binary
            # container are conclusively invalid at zero bytes.
            return None
        return BadFileItem(
            path,
            kind,
            "Empty structured file",
            "This format requires a file header and content, but the file is 0 bytes.",
        )

    try:
        with path.open("rb") as handle:
            head = handle.read(64 * 1024)
        if not head:
            return BadFileItem(path, kind, "Unreadable file", "The file returned no data when it was read.")
    except OSError as exc:
        return BadFileItem(
            path,
            kind,
            "Unreadable file",
            f"Folder Manager could not read this file. macOS reported: {exc}.",
        )

    suffix = path.suffix.lower()

    def manual_review(details: str, subject: str = "file") -> BadFileItem:
        explanation = details.strip() or f"The {subject} could not be fully verified."
        if "not proof of damage" not in explanation.casefold():
            explanation += " This is not proof of damage, but the file should be reviewed manually."
        return BadFileItem(path, kind, "Could not fully verify", explanation)

    raise_if_scan_cancelled()
    zip_document_suffixes = set(ZIP_DOCUMENT_REQUIRED_MEMBERS) | {".pages", ".numbers", ".key"}
    if suffix in zip_document_suffixes | ZIP_ARCHIVE_EXTS:
        # Password-protected modern Office files use the older encrypted OLE
        # envelope. They are valid, but cannot be inspected without a password.
        if not (suffix in OFFICE_ZIP_REQUIRED_MEMBERS and head.startswith(OLE_COMPOUND_FILE_MAGIC)):
            if suffix in {".pages", ".numbers", ".key"} and not head.startswith(b"PK"):
                return manual_review(
                    "This may be a valid legacy iWork document, but it is not a modern ZIP-based "
                    "iWork file and cannot be checked safely by this build.",
                    "iWork document",
                )
            healthy, details = validate_zip_container(path, suffix)
            if healthy is False:
                issue = (
                    "Incomplete Office document"
                    if suffix in OFFICE_ZIP_REQUIRED_MEMBERS
                    else "Incomplete document"
                    if suffix in ZIP_DOCUMENT_REQUIRED_MEMBERS
                    else "Damaged archive"
                )
                return BadFileItem(path, kind, issue, details)
            if healthy is None:
                return manual_review(details, "archive or document")
            return None
        else:
            return manual_review(
                "The Office document is encrypted. Its outer header is readable, but the "
                "document contents cannot be checked without its password.",
                "encrypted Office document",
            )

    compound_tar = path.name.casefold().endswith(
        (".tar.gz", ".tgz", ".tar.bz2", ".tbz", ".tbz2", ".tar.xz", ".txz")
    )
    if suffix == ".tar" or compound_tar:
        healthy, details = validate_tar_container(path)
        if healthy is False:
            return BadFileItem(path, kind, "Damaged archive", details)
        if healthy is None:
            return manual_review(details, "archive")
        return None
    elif suffix in {".gz", ".bz2", ".xz"}:
        healthy, details = validate_single_stream_archive(path, suffix)
        if healthy is False:
            return BadFileItem(path, kind, "Damaged archive", details)
        if healthy is None:
            return manual_review(details, "compressed file")
        return None
    elif suffix in {".rar", ".cbr", ".7z", ".cb7", ".dmg", ".pkg", ".iso"}:
        return manual_review(
            f"This build has no complete, non-destructive integrity checker for {suffix} files.",
            "archive or disk image",
        )

    if suffix in {".doc", ".xls", ".ppt"}:
        healthy, details = validate_legacy_office_container(head, suffix)
        if healthy is False:
            return BadFileItem(path, kind, "Damaged or mislabeled document", details)
        if healthy is None:
            return manual_review(details, "legacy Office document")

    if suffix == ".rtf" and not head.lstrip().startswith(b"{\\rtf"):
        return BadFileItem(
            path,
            kind,
            "Damaged or mislabeled document",
            "The file has an .rtf extension, but it does not begin with an RTF document header.",
        )

    if suffix == ".pdf":
        healthy, details = validate_pdf_structure(path, head)
        if healthy is False:
            return BadFileItem(path, kind, "Invalid or incomplete PDF", details)
        if healthy is None:
            return manual_review(details, "PDF")
        return None

    if suffix in IMAGE_EXTS:
        healthy, details = validate_image_contents(path, suffix)
        if healthy is False:
            return BadFileItem(path, kind, "Damaged or mislabeled image", details)
        if healthy is None:
            return manual_review(
                details
                or "The image format is not supported by the installed image decoder, so its "
                "pixels could not be checked.",
                "image",
            )
        return None

    if suffix in {".mid", ".midi"}:
        healthy, details = validate_midi_file(path)
        if healthy is False:
            return BadFileItem(path, kind, "Damaged or mislabeled MIDI", details)
        if healthy is None:
            return manual_review(details, "MIDI file")
        return None

    if suffix in {".sqlite", ".db"}:
        healthy, details = validate_sqlite_database(path, head, suffix)
        if healthy is False:
            return BadFileItem(path, kind, "Damaged or mislabeled database", details)
        if healthy is None:
            return manual_review(details, "database")
        return None

    if suffix in {".parquet", ".feather", ".pkl"}:
        return manual_review(
            f"This build has no safe full integrity checker for {suffix} data files.",
            "data file",
        )

    raise_if_scan_cancelled()
    if is_media_path(path, head=head):
        probe = ffprobe_path()
        meta = MediaMeta()
        if probe is not None:
            meta = scanner_media_metadata(path)
            duration = meta.duration_seconds or ffprobe_duration(path) or 0.0
        else:
            duration = 0.0

        measured_bit_rate = int(st.st_size * 8.0 / duration) if duration > 0 else meta.bit_rate_bps
        display_bit_rate = format_bitrate(measured_bit_rate or meta.bit_rate_bps)

        def media_finding(issue: str, details: str) -> BadFileItem:
            codecs = " / ".join(value for value in [meta.video_codec, meta.audio_codec] if value)
            return BadFileItem(
                path,
                kind,
                issue,
                details,
                duration=meta.duration or format_duration(duration),
                frame_rate=meta.frame_rate,
                sample_rate=meta.sample_rate,
                resolution=meta.resolution,
                bit_rate=display_bit_rate,
                codec=codecs,
            )

        if ffmpeg_path() is not None:
            is_video = is_video_path(path, head=head) or bool(meta.video_codec)
            timeline = ffmpeg_validate_media_timeline(path, duration, video=is_video)
            if timeline.healthy is False:
                issue = "Damaged video or audio" if is_video else "Damaged audio"
                return media_finding(issue, timeline.details)
            if timeline.healthy is None:
                # A complete pass can time out on unusually demanding media.
                # Sampling may still prove damage, but success is deliberately
                # treated as inconclusive rather than calling the file good.
                samples = ffmpeg_validate_media_samples(path, duration, video=is_video)
                if samples.healthy is False:
                    issue = "Damaged video" if is_video else "Damaged audio"
                    return media_finding(issue, samples.details)
                timeline_reason = timeline.details or "Complete timeline decoding did not finish."
                if samples.healthy is True:
                    sample_reason = (
                        "Distributed samples decoded successfully, but samples cannot prove that "
                        "every frame between them is intact."
                    )
                else:
                    sample_reason = samples.details or "The distributed sample check was also inconclusive."
                reasons = list(dict.fromkeys(value.strip() for value in (timeline_reason, sample_reason) if value.strip()))
                return media_finding(
                    "Could not fully verify",
                    f"{' '.join(reasons)} This is not proof of damage, but the file "
                    "should be reviewed manually.",
                )
            return None
        else:
            return media_finding(
                "Could not fully verify",
                "FFmpeg is not available, so the complete audio/video timeline was not decoded. "
                "This is not proof of damage, but the file should be reviewed manually.",
            )

    readable, details = validate_complete_file_read(path, int(st.st_size))
    if not readable:
        return BadFileItem(path, kind, "Unreadable or changing file", details)
    return None


BAD_FILE_RESULT_CACHE: Dict[Tuple[str, int, int, int, int, int], Optional[BadFileItem]] = {}
BAD_FILE_RESULT_CACHE_LOCK = threading.Lock()
BAD_FILE_RESULT_CACHE_LIMIT = 12000


def inspect_bad_file(path: Path) -> Optional[BadFileItem]:
    """Inspect an unchanged file once per app session."""

    def signature() -> Tuple[str, int, int, int, int, int]:
        stat = path.stat()
        return (
            str(path),
            int(stat.st_size),
            int(stat.st_mtime_ns),
            int(getattr(stat, "st_ctime_ns", int(stat.st_ctime * 1_000_000_000))),
            int(stat.st_dev),
            int(stat.st_ino),
        )

    try:
        cache_key = signature()
    except OSError:
        return _inspect_bad_file_uncached(path)

    with BAD_FILE_RESULT_CACHE_LOCK:
        if cache_key in BAD_FILE_RESULT_CACHE:
            return BAD_FILE_RESULT_CACHE[cache_key]

    result = _inspect_bad_file_uncached(path)
    try:
        ending_key = signature()
    except OSError:
        return BadFileItem(
            path,
            kind_for_path(path),
            "File changed during scan",
            "The file disappeared or became inaccessible before its check finished. Run the scan "
            "again after file copying, downloading, or editing has stopped.",
        )
    if ending_key != cache_key:
        return BadFileItem(
            path,
            kind_for_path(path),
            "File changed during scan",
            "The file's size or modification information changed while it was being checked, so "
            "the result was discarded. Run the scan again after the file is stable.",
        )
    with BAD_FILE_RESULT_CACHE_LOCK:
        if len(BAD_FILE_RESULT_CACHE) >= BAD_FILE_RESULT_CACHE_LIMIT:
            remove_count = max(1, BAD_FILE_RESULT_CACHE_LIMIT // 8)
            for old_key in list(BAD_FILE_RESULT_CACHE)[:remove_count]:
                BAD_FILE_RESULT_CACHE.pop(old_key, None)
        BAD_FILE_RESULT_CACHE[cache_key] = result
    return result


def duplicate_health_check(path: Path) -> Tuple[str, str, str]:
    """Translate bad-file findings into a deletion-oriented duplicate status."""
    try:
        finding = inspect_bad_file(path)
    except ScanCancelled:
        raise
    except Exception as exc:
        return (
            DUPLICATE_HEALTH_UNVERIFIED,
            "Safety check did not finish",
            f"An unexpected {type(exc).__name__} prevented a complete damage check. Review this "
            "file manually before deleting another copy.",
        )
    if finding is None:
        return (
            DUPLICATE_HEALTH_VERIFIED,
            "",
            "The complete format-specific damage check finished without finding structural or "
            "decoding errors.",
        )

    issue = str(finding.issue or "Safety check finding")
    details = str(finding.details or "Review this file before deleting another copy.")
    inconclusive_issues = {
        "Could not fully verify",
        "Check did not finish",
        "File changed during scan",
    }
    if issue in inconclusive_issues:
        return DUPLICATE_HEALTH_UNVERIFIED, issue, details
    return DUPLICATE_HEALTH_DAMAGED, issue, details


# Main-window health columns use the same format-specific inspection and cache
# as Bad File Scan.  These labels are deliberately plain: a queued check is not
# healthy, and an inconclusive check is not damage.
FILE_HEALTH_NOT_CHECKED = "Not checked"
FILE_HEALTH_CHECKING = "Checking"
FILE_HEALTH_HEALTHY = "Healthy"
FILE_HEALTH_DAMAGED = "Damaged"
FILE_HEALTH_UNABLE = "Unable"


@dataclass(frozen=True)
class FileHealthResult:
    path: Path
    status: str
    issue: str = ""
    details: str = ""
    signature: Optional[Tuple[str, int, int, int, int, int]] = None


def file_health_signature(path: Path) -> Optional[Tuple[str, int, int, int, int, int]]:
    """Return an identity that changes whenever a file needs checking again."""
    try:
        value = Path(path).expanduser()
        stat = value.stat()
        # ``Path.is_file()`` would issue a second stat call. This helper runs on
        # the GUI thread when a completed row is queued, so use the mode we
        # already read—important for large lists on external/network volumes.
        if not stat_module.S_ISREG(stat.st_mode):
            return None
        return (
            normalized_folder_path(value),
            int(stat.st_size),
            int(stat.st_mtime_ns),
            int(getattr(stat, "st_ctime_ns", int(stat.st_ctime * 1_000_000_000))),
            int(stat.st_dev),
            int(stat.st_ino),
        )
    except OSError:
        return None


FILE_HEALTH_RESULT_CACHE: Dict[str, Tuple[Tuple[str, int, int, int, int, int], FileHealthResult]] = {}
FILE_HEALTH_RESULT_CACHE_LOCK = threading.RLock()
FILE_HEALTH_RESULT_CACHE_LIMIT = 12000
ACTIVE_FILE_HEALTH_WORKERS: set = set()
ACTIVE_FILE_HEALTH_WORKERS_LOCK = threading.RLock()


def cached_file_health_result(
    path: Path,
    signature: Optional[Tuple[str, int, int, int, int, int]] = None,
) -> Optional[FileHealthResult]:
    signature = signature or file_health_signature(path)
    if signature is None:
        return None
    with FILE_HEALTH_RESULT_CACHE_LOCK:
        cached = FILE_HEALTH_RESULT_CACHE.get(signature[0])
        if cached is None or cached[0] != signature:
            return None
        return cached[1]


def cache_file_health_result(result: FileHealthResult) -> None:
    signature = result.signature
    if signature is None:
        return
    with FILE_HEALTH_RESULT_CACHE_LOCK:
        if len(FILE_HEALTH_RESULT_CACHE) >= FILE_HEALTH_RESULT_CACHE_LIMIT:
            remove_count = max(1, FILE_HEALTH_RESULT_CACHE_LIMIT // 8)
            for old_key in list(FILE_HEALTH_RESULT_CACHE)[:remove_count]:
                FILE_HEALTH_RESULT_CACHE.pop(old_key, None)
        FILE_HEALTH_RESULT_CACHE[signature[0]] = (signature, result)


def check_file_health(path: Path) -> FileHealthResult:
    """Run the canonical bad-file inspection and return a main-table status."""
    value = Path(path).expanduser()
    signature = file_health_signature(value)
    if signature is None:
        return FileHealthResult(
            value,
            FILE_HEALTH_UNABLE,
            "File is unavailable",
            "The file disappeared, is not a regular file, or cannot be read.",
            None,
        )
    cached = cached_file_health_result(value, signature)
    if cached is not None:
        return cached
    duplicate_status, issue, details = duplicate_health_check(value)
    status = {
        DUPLICATE_HEALTH_VERIFIED: FILE_HEALTH_HEALTHY,
        DUPLICATE_HEALTH_DAMAGED: FILE_HEALTH_DAMAGED,
        DUPLICATE_HEALTH_UNVERIFIED: FILE_HEALTH_UNABLE,
    }.get(duplicate_status, FILE_HEALTH_UNABLE)
    # inspect_bad_file verifies that the file did not change while it was read.
    # Capture its ending identity so a later replacement never inherits this result.
    ending_signature = file_health_signature(value)
    if ending_signature != signature:
        result = FileHealthResult(
            value,
            FILE_HEALTH_UNABLE,
            "File changed during check",
            "The result was discarded because the file changed while it was being checked.",
            ending_signature,
        )
    else:
        result = FileHealthResult(value, status, str(issue or ""), str(details or ""), signature)
    cache_file_health_result(result)
    return result


# ---------------------------------------------------------------------------
# Background file health coordination


class FileHealthBatchWorker(QThread):
    """Low-concurrency worker used by passive main-window health columns."""

    progress = Signal(str, int)
    result_ready = Signal(object)

    def __init__(self, paths: Iterable[Path]):
        super().__init__()
        self.paths = list(dict.fromkeys(Path(path).expanduser() for path in paths))
        self._cancel_requested = False
        register_scan_worker(self)

    def request_cancel(self):
        self._cancel_requested = True
        self.requestInterruption()
        cancel_scan_processes(self)

    def run(self):
        executor: Optional[concurrent.futures.ThreadPoolExecutor] = None
        try:
            worker_count = max(1, min(2, BAD_FILE_SCAN_WORKERS, len(self.paths)))
            executor = concurrent.futures.ThreadPoolExecutor(
                max_workers=worker_count,
                thread_name_prefix="file-health-column",
            )
            futures = {
                executor.submit(run_scan_task, self, check_file_health, path): path
                for path in self.paths
            }
            completed = 0
            for future in concurrent.futures.as_completed(futures):
                if self._cancel_requested or self.isInterruptionRequested():
                    break
                path = futures[future]
                try:
                    result = future.result()
                except (ScanCancelled, concurrent.futures.CancelledError):
                    continue
                except Exception as exc:
                    result = FileHealthResult(
                        path,
                        FILE_HEALTH_UNABLE,
                        "Check did not finish",
                        f"The background check stopped unexpectedly ({type(exc).__name__}).",
                        file_health_signature(path),
                    )
                completed += 1
                self.progress.emit(
                    f"Checking file health {completed}/{len(self.paths)}",
                    int(100 * completed / max(1, len(self.paths))),
                )
                self.result_ready.emit(result)
        finally:
            if executor is not None:
                executor.shutdown(wait=True, cancel_futures=True)
            cancel_scan_processes(self)


class FileHealthCoordinator(QObject):
    """Queue cached health checks without doing filesystem/media work on Qt's UI thread."""

    result_ready = Signal(object)

    def __init__(self, parent: Optional[QObject] = None):
        super().__init__(parent)
        self._pending: Dict[str, Path] = {}
        self._active_paths: set[str] = set()
        self._worker: Optional[FileHealthBatchWorker] = None
        self._closed = False
        self._paused = False
        self._start_timer = QTimer(self)
        self._start_timer.setSingleShot(True)
        self._start_timer.timeout.connect(self._start_next_batch)

    @staticmethod
    def checking_result(
        path: Path,
        signature: Optional[Tuple[str, int, int, int, int, int]] = None,
    ) -> FileHealthResult:
        value = Path(path).expanduser()
        return FileHealthResult(
            value,
            FILE_HEALTH_CHECKING,
            "",
            "Damage check is queued or running.",
            signature or file_health_signature(value),
        )

    def request(self, path: Path) -> FileHealthResult:
        value = Path(path).expanduser()
        # One stat per request. The previous cached/missing/checking sequence
        # performed the same filesystem lookup three times per visible row.
        signature = file_health_signature(value)
        cached = cached_file_health_result(value, signature) if signature is not None else None
        if cached is not None:
            return cached
        if signature is None:
            return FileHealthResult(
                value,
                FILE_HEALTH_UNABLE,
                "File is unavailable",
                "The file disappeared, is not a regular file, or cannot be read.",
                None,
            )
        key = normalized_folder_path(value)
        if not self._closed and key not in self._active_paths:
            self._pending.setdefault(key, value)
            if not self._paused and self._worker is None and not self._start_timer.isActive():
                # Coalesce rows added during one incremental table-population frame.
                self._start_timer.start(40)
        return self.checking_result(value, signature)

    def set_paused(self, paused: bool):
        """Defer new batches while a large native table is being constructed."""
        self._paused = bool(paused)
        if self._paused:
            self._start_timer.stop()
        elif not self._closed and self._worker is None and self._pending:
            self._start_timer.start(0)

    def _start_next_batch(self):
        if self._closed or self._paused or self._worker is not None or not self._pending:
            return
        # Short batches make cancellation quick and let newly visible/completed
        # files join the pipeline without allocating thousands of futures at once.
        keys = list(self._pending)[:48]
        paths = [self._pending.pop(key) for key in keys]
        self._active_paths.update(keys)
        worker = FileHealthBatchWorker(paths)
        self._worker = worker
        with ACTIVE_FILE_HEALTH_WORKERS_LOCK:
            ACTIVE_FILE_HEALTH_WORKERS.add(worker)
        worker.result_ready.connect(self._on_result)
        worker.finished.connect(lambda current=worker, active_keys=tuple(keys): self._on_finished(current, active_keys))
        worker.start()

    def _on_result(self, result: FileHealthResult):
        if not self._closed:
            self.result_ready.emit(result)

    def _on_finished(self, worker: FileHealthBatchWorker, active_keys: Tuple[str, ...]):
        with ACTIVE_FILE_HEALTH_WORKERS_LOCK:
            ACTIVE_FILE_HEALTH_WORKERS.discard(worker)
        self._active_paths.difference_update(active_keys)
        if self._worker is worker:
            self._worker = None
        worker.deleteLater()
        if not self._closed and self._pending:
            self._start_timer.start(0)

    def close(self):
        self._closed = True
        self._pending.clear()
        self._start_timer.stop()
        worker = self._worker
        if worker is not None:
            worker.request_cancel()

    def running_worker(self) -> Optional[QThread]:
        worker = self._worker
        if worker is None:
            return None
        try:
            return worker if worker.isRunning() else None
        except RuntimeError:
            return None


# ---------------------------------------------------------------------------
# Bad-file scanning


class BadFileWorker(QThread):
    progress = Signal(str, int)
    found = Signal(object)
    results_ready = Signal(list)
    failed = Signal(str)
    cancelled = Signal()

    def __init__(self, folder: Path, scan_files: Optional[List[Path]] = None):
        super().__init__()
        register_scan_worker(self)
        self.folder = folder
        self.scan_files = list(scan_files) if scan_files is not None else None
        self._cancel_requested = False
        self._allowed_removed_lock = threading.RLock()
        self._allowed_removed_paths: set[Path] = set()

    def request_cancel(self):
        self._cancel_requested = True
        cancel_scan_processes(self)

    def check_cancel(self):
        if self._cancel_requested or self.isInterruptionRequested():
            raise ScanCancelled()

    def allow_paths_removed(self, paths: Iterable[Path]):
        with self._allowed_removed_lock:
            self._allowed_removed_paths.update(Path(path) for path in paths)

    def allowed_removed_paths(self) -> set[Path]:
        with self._allowed_removed_lock:
            return set(self._allowed_removed_paths)

    def verify_scan_scope_unchanged(self, files: Sequence[Path]):
        if self.scan_files is not None:
            return
        self.progress.emit("Confirming the folder did not change during the scan…", -1)
        stable = False
        change_count = 0
        for _attempt in range(2):
            stable, change_count = recursive_file_set_is_stable(
                self.folder,
                files,
                cancel_check=self.check_cancel,
                allowed_missing_paths=self.allowed_removed_paths(),
            )
            if stable:
                break
        if not stable:
            raise RuntimeError(
                "The folder changed or became partly inaccessible while the bad-file scan was "
                f"running ({human_count(change_count)} changed or unreadable location(s)). The "
                "scan stopped instead of treating a stale result as complete. Wait for file "
                "operations to finish, then run it again."
            )

    def run(self):
        try:
            self.progress.emit("Finding files to check…", -1)

            def report_enumeration(count: int, _folder: Path):
                self.progress.emit(f"Finding files… {human_count(count)} found", -1)

            discovery_errors: List[OSError] = []
            files = (
                list(self.scan_files)
                if self.scan_files is not None
                else list_files_recursive(
                    self.folder,
                    progress_callback=report_enumeration,
                    cancel_check=self.check_cancel,
                    error_callback=discovery_errors.append,
                )
            )
            if discovery_errors:
                raise RuntimeError(
                    "Folder Manager could not read "
                    f"{human_count(len(discovery_errors))} folder location(s), so the bad-file scan "
                    "stopped instead of treating skipped files as good. Check folder permissions "
                    "and disk connections, then run it again."
                )
            self.check_cancel()

            media_file_count = sum(1 for path in files if is_media_path(path))
            if media_file_count and ffmpeg_path() is None:
                raise RuntimeError(
                    "Folder Manager found "
                    f"{human_count(media_file_count)} media file(s), but FFmpeg is not available. "
                    "Those files cannot be classified reliably, so the scan stopped instead of "
                    "calling unchecked files good. Install FFmpeg, then run the scan again."
                )

            file_count = len(files)

            def estimated_scan_cost(path: Path) -> Tuple[int, int, str]:
                nonlocal prepared_count, last_prepare_progress_at
                self.check_cancel()
                media_cost = 1 if is_media_path(path) else 0
                try:
                    size = int(path.stat().st_size)
                except OSError:
                    size = 0
                prepared_count += 1
                now = time.monotonic()
                if now - last_prepare_progress_at >= 0.5:
                    last_prepare_progress_at = now
                    self.progress.emit(
                        f"Preparing checks… {human_count(prepared_count)}/{human_count(file_count)}",
                        -1,
                    )
                return media_cost, size, str(path).casefold()

            # Quick documents/images and smaller media establish visible progress
            # before multi-hour videos occupy every decoder.
            prepared_count = 0
            last_prepare_progress_at = 0.0
            files.sort(key=estimated_scan_cost)
            bad_items: List[BadFileItem] = []
            total = max(1, len(files))
            progress_estimate = ScannerProgressEstimate(files)
            # This shares the measured process-wide media limit with Duplicate
            # Scan, so two open scanners reuse work without doubling decoders.
            max_workers = BAD_FILE_SCAN_WORKERS
            pending: Dict[concurrent.futures.Future, Path] = {}
            iterator = iter(files)
            completed = 0

            executor = concurrent.futures.ThreadPoolExecutor(
                max_workers=max_workers,
                thread_name_prefix="bad-file-scan",
            )
            try:
                def submit_until_full():
                    while len(pending) < max_workers * 2:
                        self.check_cancel()
                        try:
                            path = next(iterator)
                        except StopIteration:
                            return
                        pending[
                            executor.submit(
                                run_scan_task,
                                self,
                                inspect_bad_file,
                                path,
                            )
                        ] = path

                submit_until_full()
                self.progress.emit(
                    f"Checking {human_count(len(files))} file(s) • {min(max_workers, len(pending))} active",
                    -1 if files else 100,
                )
                last_heartbeat_at = 0.0
                while pending:
                    self.check_cancel()
                    done, _not_done = concurrent.futures.wait(
                        pending,
                        timeout=0.15,
                        return_when=concurrent.futures.FIRST_COMPLETED,
                    )
                    if not done:
                        now = time.monotonic()
                        if now - last_heartbeat_at >= 0.75:
                            last_heartbeat_at = now
                            active = min(max_workers, len(pending))
                            self.progress.emit(
                                f"Deep-checking {active} file(s) • {human_count(completed)}/{human_count(len(files))} complete • {progress_estimate.eta_text()}",
                                progress_estimate.percent() if completed else -1,
                            )
                        continue

                    for future in done:
                        path = pending.pop(future)
                        completed += 1
                        try:
                            item = future.result()
                        except ScanCancelled:
                            raise
                        except Exception as exc:
                            item = BadFileItem(
                                path,
                                kind_for_path(path),
                                "Check did not finish",
                                "Folder Manager encountered an unexpected problem while checking "
                                f"this file ({type(exc).__name__}). This is not proof that the file "
                                "is damaged; try scanning it again.",
                            )
                        if item:
                            bad_items.append(item)
                            self.found.emit(item)
                        progress_estimate.complete(path)
                        self.progress.emit(
                            f"{progress_estimate.text('Checking', total, path.name)} | {max_workers} workers",
                            progress_estimate.percent(),
                        )
                    submit_until_full()
            except ScanCancelled:
                cancel_scan_processes(self)
                executor.shutdown(wait=False, cancel_futures=True)
                raise
            finally:
                executor.shutdown(wait=False, cancel_futures=True)
            self.verify_scan_scope_unchanged(files)
            self.results_ready.emit(bad_items)
        except ScanCancelled:
            self.cancelled.emit()
        except Exception as exc:
            debug_log("bad-file-scan", "worker failed", error_type=type(exc).__name__, error=str(exc))
            self.failed.emit(
                str(exc).strip()
                or "The bad-file scan stopped because of an unexpected internal error."
            )


# ---------------------------------------------------------------------------
# Bad-file results dialog


class BadFileDialog(ScannerDialogBase):
    ROLE_PATH = Qt.UserRole
    ROLE_KIND = Qt.UserRole + 1
    ROLE_ISSUE = Qt.UserRole + 2
    ROLE_SIZE = Qt.UserRole + 3
    ROLE_FOLDER = Qt.UserRole + 4
    LOCATION_COLUMN = 9
    DETAILS_COLUMN = 10

    def __init__(self, folder: Path, parent=None, scan_files: Optional[List[Path]] = None):
        super().__init__(None)
        self.owner_window = top_level_window_for(parent)
        self.setWindowFlag(Qt.Window, True)
        self.setWindowModality(Qt.NonModal)
        self.setModal(False)
        try:
            self.setWindowFlag(Qt.WindowType.WindowFullscreenButtonHint, True)
        except Exception:
            pass
        self.setWindowTitle("Bad File Scan")
        self.resize(1050, 650)
        self.folder = folder
        self.scan_files = list(scan_files) if scan_files is not None else None
        self.worker: Optional[BadFileWorker] = None
        self.retired_workers: List[BadFileWorker] = []
        self.close_after_scan_stops = False
        self.items: List[BadFileItem] = []
        self.bad_item_keys: set[Tuple[str, str]] = set()
        self.reason_items: Dict[str, List[BadFileItem]] = {}
        self.reason_folder_items: Dict[str, Dict[str, List[BadFileItem]]] = {}
        self.deleted_bad_items_by_path: Dict[Path, List[BadFileItem]] = defaultdict(list)
        self.suppressed_paths: set[Path] = set()
        self.undo_stack: List[TrashAction] = []
        self.redo_stack: List[TrashAction] = []
        self.trash_workers: List[TrashMoveWorker] = []
        self.quicklook_dialog: Optional[LargePreviewDialog] = None
        self.last_preview_toggle_at = 0.0
        self.filtering_selection = False
        self.renaming_item: Optional[QTreeWidgetItem] = None
        self.renaming_path: Optional[Path] = None
        self.rename_suppress = False
        self.pending_bad_preview_path: Optional[Path] = None
        self.debug_last_selected_path: Optional[Path] = None
        self.bad_preview_timer = QTimer(self)
        self.bad_preview_timer.setSingleShot(True)
        self.bad_preview_timer.timeout.connect(self.apply_pending_bad_preview)
        self.bad_results_timer = QTimer(self)
        self.bad_results_timer.setSingleShot(True)
        self.bad_results_timer.timeout.connect(self.flush_bad_results)
        self.pending_bad_items: List[BadFileItem] = []
        self.bad_file_size_cache: Dict[str, int] = {}
        self.reason_header_items: Dict[str, QTreeWidgetItem] = {}
        self.folder_header_items: Dict[Tuple[str, str], QTreeWidgetItem] = {}
        self.reason_size_totals: Dict[str, int] = defaultdict(int)
        self.folder_size_totals: Dict[Tuple[str, str], int] = defaultdict(int)
        self.scan_progress_text = "Ready"
        self.pending_details_column_width = 0
        self.details_column_timer = QTimer(self)
        self.details_column_timer.setSingleShot(True)
        self.details_column_timer.timeout.connect(self.apply_details_column_width)

        layout = QVBoxLayout(self)
        layout.setContentsMargins(14, 14, 14, 14)
        layout.setSpacing(10)

        header = QHBoxLayout()
        layout.addLayout(header)
        title_box = QVBoxLayout()
        title_box.setSpacing(1)
        title = QLabel("Bad File Scan")
        title.setObjectName("SectionTitle")
        scan_scope = str(folder)
        if self.scan_files is not None:
            scan_scope += f" • {human_count(len(self.scan_files))} visible/open file(s)"
        subtitle = QLabel(scan_scope)
        subtitle.setObjectName("MutedLabel")
        subtitle.setWordWrap(True)
        subtitle.setTextInteractionFlags(Qt.TextSelectableByMouse)
        subtitle.setSizePolicy(QSizePolicy.Ignored, QSizePolicy.Preferred)
        subtitle.setToolTip(scan_scope)
        title_box.addWidget(title)
        title_box.addWidget(subtitle)
        header.addLayout(title_box, stretch=1)
        self.scan_btn = QPushButton("Start Scan")
        self.scan_btn.setObjectName("BrightGreyButton")
        self.undo_btn = QPushButton("Undo")
        self.undo_btn.setEnabled(False)
        self.close_btn = QPushButton("Close")
        header.addWidget(self.scan_btn)
        header.addWidget(self.undo_btn)
        header.addWidget(self.close_btn)

        progress_row = QHBoxLayout()
        layout.addLayout(progress_row)
        self.progress_label = QLabel("Ready")
        self.progress_label.setObjectName("MutedLabel")
        self.progress_label.setMinimumWidth(0)
        self.progress_label.setSizePolicy(QSizePolicy.Ignored, QSizePolicy.Fixed)
        self.progress = QProgressBar()
        self.progress.setTextVisible(False)
        self.progress.setFixedWidth(420)
        self.progress.setFixedHeight(12)
        self.progress.setVisible(False)
        progress_row.addWidget(self.progress_label, stretch=1)
        progress_row.addWidget(self.progress)

        self.preview_panel = PreviewPanel("Select a scan finding to preview it here.")
        self.preview_panel.zoomRequested.connect(self.zoom_current_preview)
        layout.addWidget(self.preview_panel)

        self.tree = FileTreeWidget()
        self.tree.return_renames = True
        self.tree.setColumnCount(11)
        self.tree.setHeaderLabels(
            [
                "File", "Kind", "Issue", "Size", "Duration", "Frame Rate",
                "Sample Rate", "Resolution", "Bitrate", "Location", "Details",
            ]
        )
        self.tree.setRootIsDecorated(False)
        self.tree.setUniformRowHeights(True)
        self.tree.setAnimated(False)
        self.tree.setAlternatingRowColors(True)
        self.tree.setSelectionBehavior(QAbstractItemView.SelectRows)
        self.tree.setSelectionMode(QAbstractItemView.ExtendedSelection)
        self.tree.setEditTriggers(QAbstractItemView.NoEditTriggers)
        self.tree.setTextElideMode(Qt.ElideNone)
        self.tree.header().setSectionsMovable(True)
        self.tree.header().setStretchLastSection(False)
        for column, width in enumerate([420, 110, 210, 105, 105, 105, 120, 120, 110, 360, 390]):
            self.tree.header().setSectionResizeMode(column, QHeaderView.Interactive)
            self.tree.setColumnWidth(column, width)
        restore_tree_header_state(self.tree, "bad_files_v3")
        self.tree.header().setStretchLastSection(False)
        connect_tree_header_persistence(self.tree, "bad_files_v3")
        self.tree.itemSelectionChanged.connect(self.update_preview)
        self.tree.itemDoubleClicked.connect(self.open_tree_item)
        self.tree.customContextMenuRequested.connect(self.open_context_menu)
        self.tree.setContextMenuPolicy(Qt.CustomContextMenu)
        self.tree.deletePressed.connect(self.move_selected_to_trash)
        self.tree.undoPressed.connect(self.undo_trash)
        self.tree.redoPressed.connect(self.redo_trash)
        self.tree.openPressed.connect(self.open_current)
        self.tree.previewPressed.connect(self.zoom_current_preview)
        self.tree.reviewStepPressed.connect(self.open_adjacent_file)
        self.tree.playPausePressed.connect(self.toggle_active_preview_playback)
        self.tree.renamePressed.connect(self.rename_current_item)
        self.tree.blankClicked.connect(self.clear_bad_file_selection)
        self.tree.disclosurePressed.connect(self.toggle_bad_reason_header)
        self.tree.itemExpanded.connect(self.sync_bad_header_expansion)
        self.tree.itemCollapsed.connect(self.sync_bad_header_expansion)
        self.tree.itemChanged.connect(self.on_item_changed)
        layout.addWidget(self.tree, stretch=1)

        self.scan_btn.clicked.connect(self.handle_scan_button)
        self.undo_btn.clicked.connect(self.undo_trash)
        self.close_btn.clicked.connect(self.close)
        self.preview_shortcut = QShortcut(QKeySequence(Qt.Key_Space), self)
        self.preview_shortcut.setContext(Qt.WindowShortcut)
        self.preview_shortcut.activated.connect(self.trigger_preview_shortcut)
        configure_settled_window_geometry(self, "bad_file_scan", QSize(1050, 650))

    def bad_file_size(self, path: Path) -> int:
        key = normalized_folder_path(path)
        size = self.bad_file_size_cache.get(key)
        if size is not None:
            return size
        try:
            size = path.stat().st_size
        except OSError:
            size = 0
        self.bad_file_size_cache[key] = size
        return size

    def trigger_preview_shortcut(self):
        if self.renaming_item is not None:
            return
        if self.tree.state() == QAbstractItemView.EditingState:
            return
        self.zoom_current_preview()

    def start_scan(self):
        self.close_after_scan_stops = False
        self.items = []
        self.bad_item_keys = set()
        self.reason_items = {}
        self.reason_folder_items = {}
        self.reason_header_items = {}
        self.folder_header_items = {}
        self.reason_size_totals = defaultdict(int)
        self.folder_size_totals = defaultdict(int)
        self.pending_bad_items = []
        self.bad_file_size_cache = {}
        self.bad_results_timer.stop()
        self.deleted_bad_items_by_path = defaultdict(list)
        self.suppressed_paths = set()
        self.undo_stack = []
        self.redo_stack = []
        self.update_undo_button()
        self.tree.clear()
        self.progress.setRange(0, 0)
        self.progress.setValue(0)
        self.progress.setVisible(True)
        self.scan_progress_text = "Finding files to check…"
        self.progress_label.setText(self.scan_progress_text)
        self.scan_btn.setText("Terminate")
        self.close_btn.setEnabled(False)
        self.worker = BadFileWorker(self.folder, scan_files=self.scan_files)
        self.worker.progress.connect(self.on_progress)
        self.worker.found.connect(self.add_bad_item)
        self.worker.results_ready.connect(self.on_finished)
        self.worker.failed.connect(self.on_failed)
        self.worker.cancelled.connect(self.on_cancelled)
        self.worker.start()

    def signal_worker(self) -> Optional[BadFileWorker]:
        sender = self.sender()
        if isinstance(sender, BadFileWorker):
            return sender
        return self.worker

    def finish_scan_controls(self):
        self.scan_btn.setEnabled(True)
        self.scan_btn.setText("Start Scan")
        self.close_btn.setEnabled(True)
        self.progress.setVisible(False)

    def on_progress(self, text: str, value: int):
        self.scan_progress_text = text
        set_elided_label_text(self.progress_label, f"{text}  |  Found {human_count(len(self.items))} finding(s)")
        if value < 0:
            if self.progress.minimum() != 0 or self.progress.maximum() != 0:
                self.progress.setRange(0, 0)
        else:
            if self.progress.minimum() != 0 or self.progress.maximum() != 100:
                self.progress.setRange(0, 100)
            self.progress.setValue(max(0, min(100, value)))

    def add_bad_item(self, item: BadFileItem):
        if item.file in self.suppressed_paths:
            return
        key = (str(item.file), item.issue)
        if key in self.bad_item_keys:
            return
        self.bad_item_keys.add(key)
        self.items.append(item)
        self.reason_items.setdefault(item.issue, []).append(item)
        folder_key = self.bad_folder_key(item.file)
        self.reason_folder_items.setdefault(item.issue, {}).setdefault(folder_key, []).append(item)
        self.pending_bad_items.append(item)
        batch_size = SCANNER_RESULT_BATCH_ROWS
        delay = 75
        if len(self.pending_bad_items) >= batch_size:
            self.flush_bad_results()
        elif not self.bad_results_timer.isActive():
            self.bad_results_timer.start(delay)
        set_elided_label_text(
            self.progress_label,
            f"{self.scan_progress_text}  |  Found {human_count(len(self.items))} finding(s)",
        )

    def flush_bad_results(self):
        if not self.pending_bad_items:
            return
        pending = [item for item in self.pending_bad_items if item.file not in self.suppressed_paths]
        self.pending_bad_items = []
        if not pending:
            return
        affected_issues = {item.issue for item in pending}
        affected_folders = {(item.issue, self.bad_folder_key(item.file)) for item in pending}
        previous_block = self.tree.blockSignals(True)
        previous_updates = self.tree.updatesEnabled()
        self.tree.setUpdatesEnabled(False)
        try:
            longest_details = ""
            for item in pending:
                self.append_bad_item_to_tree(item, update_header=False)
                if len(item.details) > len(longest_details):
                    longest_details = item.details
            for issue in affected_issues:
                self.update_reason_header_item(self.reason_header_for_issue(issue))
            for issue, folder_key in affected_folders:
                self.update_folder_header_item(self.folder_header_for_key(issue, folder_key))
            self.request_details_column_width(longest_details)
        finally:
            self.tree.blockSignals(previous_block)
            self.tree.setUpdatesEnabled(previous_updates)
            self.tree.viewport().update()

    def on_finished(self, items: List[BadFileItem]):
        worker = self.signal_worker()
        items = [item for item in items if item.file not in self.suppressed_paths]
        self.bad_results_timer.stop()
        self.flush_bad_results()
        self.retire_worker(worker)
        self.items = items
        self.bad_item_keys = {(str(item.file), item.issue) for item in items}
        # Results were already inserted as they arrived. Rebuilding the whole
        # tree here made a completed large scan appear frozen a second time.
        self.rebuild_reason_indexes()
        self.finish_scan_controls()
        self.progress_label.setText(f"{human_count(len(items))} finding(s) found")
        self.update_undo_button()
        self.maybe_close_after_scan_stops()

    def on_failed(self, message: str):
        worker = self.signal_worker()
        self.bad_results_timer.stop()
        self.pending_bad_items = []
        self.retire_worker(worker)
        self.finish_scan_controls()
        self.progress_label.setText("Scan failed")
        QMessageBox.warning(self, "Bad file scan failed", message)
        self.maybe_close_after_scan_stops()

    def on_cancelled(self):
        worker = self.signal_worker()
        self.bad_results_timer.stop()
        self.flush_bad_results()
        self.retire_worker(worker)
        self.finish_scan_controls()
        self.progress_label.setText(f"Scan terminated  |  {human_count(len(self.items))} finding(s) kept")
        self.update_undo_button()
        self.maybe_close_after_scan_stops()

    def tree_item_for_bad_file(self, bad: BadFileItem) -> QTreeWidgetItem:
        byte_size = self.bad_file_size(bad.file)
        size = human_size(byte_size) if byte_size else "?"
        values = [
            bad.file.name,
            bad.kind,
            bad.issue,
            size,
            bad.duration or "--",
            bad.frame_rate or "--",
            bad.sample_rate or "--",
            bad.resolution or "--",
            bad.bit_rate or "--",
            str(bad.file.parent),
            bad.details,
        ]
        item = QTreeWidgetItem(values)
        item.setData(0, self.ROLE_PATH, str(bad.file))
        item.setData(0, self.ROLE_KIND, "file")
        item.setData(0, self.ROLE_ISSUE, bad.issue)
        item.setData(0, self.ROLE_SIZE, byte_size)
        item.setFlags(item.flags() | Qt.ItemIsEditable)
        tooltip_values = list(values)
        tooltip_values[0] = str(bad.file)
        for column, value in enumerate(tooltip_values):
            item.setToolTip(column, value)
        return item

    def create_reason_header(self, issue: str, items: List[BadFileItem], expanded: bool = True) -> QTreeWidgetItem:
        header = QTreeWidgetItem([self.reason_header_text(issue, items, expanded=expanded)] + [""] * (self.tree.columnCount() - 1))
        header.setData(0, self.ROLE_KIND, "reason")
        header.setData(0, self.ROLE_ISSUE, issue)
        header.setTextAlignment(0, Qt.AlignLeft | Qt.AlignVCenter)
        for column in range(self.tree.columnCount()):
            header.setBackground(column, QColor("#2b2b2b"))
            header.setForeground(column, QColor("#f4f4f6"))
            font = header.font(column)
            font.setBold(True)
            header.setFont(column, font)
            header.setSizeHint(column, QSize(0, 32))
            header.setToolTip(column, header.text(0))
        header.setFirstColumnSpanned(True)
        header.setExpanded(expanded)
        return header

    def bad_folder_key(self, path: Path) -> str:
        return normalized_folder_path(path.parent)

    def bad_folder_label(self, folder_key: str) -> str:
        folder = Path(folder_key)
        scan_root = Path(normalized_folder_path(self.folder))
        try:
            relative = folder.relative_to(scan_root)
        except ValueError:
            return str(folder)
        return "Current folder" if str(relative) == "." else str(relative)

    def folder_header_text(
        self,
        issue: str,
        folder_key: str,
        items: List[BadFileItem],
        expanded: bool = True,
    ) -> str:
        marker = "▼" if expanded else "▶"
        size = self.folder_size_totals.get((issue, folder_key))
        if size is None:
            size = sum(self.bad_file_size(item.file) for item in items)
        return (
            f"{marker} Folder: {self.bad_folder_label(folder_key)} "
            f"({human_count(len(items))} files)  |  {human_size(size)}"
        )

    def create_folder_header(
        self,
        issue: str,
        folder_key: str,
        items: List[BadFileItem],
        expanded: bool = True,
    ) -> QTreeWidgetItem:
        header = QTreeWidgetItem(
            [self.folder_header_text(issue, folder_key, items, expanded=expanded)]
            + [""] * (self.tree.columnCount() - 1)
        )
        header.setData(0, self.ROLE_KIND, "folder_group")
        header.setData(0, self.ROLE_ISSUE, issue)
        header.setData(0, self.ROLE_FOLDER, folder_key)
        header.setData(0, self.ROLE_PATH, folder_key)
        header.setTextAlignment(0, Qt.AlignLeft | Qt.AlignVCenter)
        for column in range(self.tree.columnCount()):
            header.setBackground(column, QColor("#303138"))
            header.setForeground(column, QColor("#d8d9df"))
            font = header.font(column)
            font.setBold(True)
            header.setFont(column, font)
            header.setSizeHint(column, QSize(0, 30))
            header.setToolTip(column, folder_key)
        header.setFirstColumnSpanned(True)
        header.setExpanded(expanded)
        return header

    def reason_header_for_issue(self, issue: str) -> Optional[QTreeWidgetItem]:
        header = self.reason_header_items.get(issue)
        if header is not None and self.tree.indexOfTopLevelItem(header) >= 0:
            return header
        self.reason_header_items.pop(issue, None)
        for index in range(self.tree.topLevelItemCount()):
            candidate = self.tree.topLevelItem(index)
            if str(candidate.data(0, self.ROLE_ISSUE) or "") == issue:
                self.reason_header_items[issue] = candidate
                return candidate
        return None

    def folder_header_for_key(self, issue: str, folder_key: str) -> Optional[QTreeWidgetItem]:
        cache_key = (issue, folder_key)
        header = self.folder_header_items.get(cache_key)
        if header is not None:
            parent = header.parent()
            if (
                parent is not None
                and parent.data(0, self.ROLE_KIND) == "reason"
                and str(parent.data(0, self.ROLE_ISSUE) or "") == issue
            ):
                return header
        self.folder_header_items.pop(cache_key, None)
        reason_header = self.reason_header_for_issue(issue)
        if reason_header is None:
            return None
        for index in range(reason_header.childCount()):
            candidate = reason_header.child(index)
            if (
                candidate.data(0, self.ROLE_KIND) == "folder_group"
                and str(candidate.data(0, self.ROLE_FOLDER) or "") == folder_key
            ):
                self.folder_header_items[cache_key] = candidate
                return candidate
        return None

    def append_bad_item_to_tree(self, bad: BadFileItem, update_header: bool = True):
        header = self.reason_header_for_issue(bad.issue)
        if header is None:
            header = self.create_reason_header(bad.issue, self.reason_items.get(bad.issue, []), expanded=True)
            insert_at = self.tree.topLevelItemCount()
            for index in range(self.tree.topLevelItemCount()):
                existing_issue = str(self.tree.topLevelItem(index).data(0, self.ROLE_ISSUE) or "")
                if bad.issue.casefold() < existing_issue.casefold():
                    insert_at = index
                    break
            self.tree.insertTopLevelItem(insert_at, header)
            header.setExpanded(True)
            self.reason_header_items[bad.issue] = header

        folder_key = self.bad_folder_key(bad.file)
        folder_header = self.folder_header_for_key(bad.issue, folder_key)
        if folder_header is None:
            folder_items = self.reason_folder_items.get(bad.issue, {}).get(folder_key, [])
            folder_header = self.create_folder_header(bad.issue, folder_key, folder_items, expanded=True)
            insert_at = header.childCount()
            new_label = self.bad_folder_label(folder_key).casefold()
            for index in range(header.childCount()):
                existing = header.child(index)
                existing_key = str(existing.data(0, self.ROLE_FOLDER) or "")
                if new_label < self.bad_folder_label(existing_key).casefold():
                    insert_at = index
                    break
            header.insertChild(insert_at, folder_header)
            folder_header.setExpanded(True)
            self.folder_header_items[(bad.issue, folder_key)] = folder_header

        file_item = self.tree_item_for_bad_file(bad)
        insert_at = folder_header.childCount()
        new_name = bad.file.name.casefold()
        for index in range(folder_header.childCount()):
            existing_path = self.item_path(folder_header.child(index))
            if existing_path is not None and new_name < existing_path.name.casefold():
                insert_at = index
                break
        folder_header.insertChild(insert_at, file_item)
        byte_size = self.bad_file_size(bad.file)
        self.reason_size_totals[bad.issue] += byte_size
        self.folder_size_totals[(bad.issue, folder_key)] += byte_size
        header.setExpanded(True)
        folder_header.setExpanded(True)
        if update_header:
            self.update_reason_header_item(header)
            self.update_folder_header_item(folder_header)

    def reason_header_text(self, issue: str, items: List[BadFileItem], expanded: bool = True) -> str:
        marker = "▼" if expanded else "▶"
        size = self.reason_size_totals.get(issue)
        if size is None:
            size = 0
            for item in items:
                size += self.bad_file_size(item.file)
        return f"{marker} {issue} ({human_count(len(items))} files)  |  {human_size(size)}"

    def rebuild_reason_indexes(self):
        self.reason_items = defaultdict(list)
        self.reason_folder_items = {}
        self.reason_size_totals = defaultdict(int)
        self.folder_size_totals = defaultdict(int)
        for item in self.items:
            if not item.file.exists() or item.file in self.suppressed_paths:
                continue
            folder_key = self.bad_folder_key(item.file)
            self.reason_items[item.issue].append(item)
            self.reason_folder_items.setdefault(item.issue, {}).setdefault(folder_key, []).append(item)
            byte_size = self.bad_file_size(item.file)
            self.reason_size_totals[item.issue] += byte_size
            self.folder_size_totals[(item.issue, folder_key)] += byte_size
        self.reason_header_items = {}
        self.folder_header_items = {}
        for index in range(self.tree.topLevelItemCount()):
            header = self.tree.topLevelItem(index)
            issue = str(header.data(0, self.ROLE_ISSUE) or "")
            if issue:
                self.reason_header_items[issue] = header
                for child_index in range(header.childCount()):
                    folder_header = header.child(child_index)
                    if folder_header.data(0, self.ROLE_KIND) != "folder_group":
                        continue
                    folder_key = str(folder_header.data(0, self.ROLE_FOLDER) or "")
                    self.folder_header_items[(issue, folder_key)] = folder_header
                    self.update_folder_header_item(folder_header)
                self.update_reason_header_item(header)

    def populate_reason_tree(self, preserve_selection: bool = False):
        selected_paths = self.selected_paths() if preserve_selection else []
        current_path = self.current_path() if preserve_selection else None
        expanded_reasons = {
            str(self.tree.topLevelItem(i).data(0, self.ROLE_ISSUE) or ""):
            self.tree.topLevelItem(i).isExpanded()
            for i in range(self.tree.topLevelItemCount())
        }
        expanded_folders: Dict[Tuple[str, str], bool] = {}
        for top_index in range(self.tree.topLevelItemCount()):
            reason_header = self.tree.topLevelItem(top_index)
            issue = str(reason_header.data(0, self.ROLE_ISSUE) or "")
            for child_index in range(reason_header.childCount()):
                folder_header = reason_header.child(child_index)
                if folder_header.data(0, self.ROLE_KIND) != "folder_group":
                    continue
                folder_key = str(folder_header.data(0, self.ROLE_FOLDER) or "")
                expanded_folders[(issue, folder_key)] = folder_header.isExpanded()
        scroll_value = self.tree.verticalScrollBar().value()

        previous_block = self.tree.blockSignals(True)
        previous_updates = self.tree.updatesEnabled()
        self.tree.setUpdatesEnabled(False)
        try:
            self.tree.clear()
            self.reason_header_items = {}
            self.folder_header_items = {}
            self.reason_items = defaultdict(list)
            self.reason_folder_items = {}
            self.reason_size_totals = defaultdict(int)
            self.folder_size_totals = defaultdict(int)
            for item in self.items:
                if item.file.exists() and item.file not in self.suppressed_paths:
                    folder_key = self.bad_folder_key(item.file)
                    self.reason_items[item.issue].append(item)
                    self.reason_folder_items.setdefault(item.issue, {}).setdefault(folder_key, []).append(item)
                    byte_size = self.bad_file_size(item.file)
                    self.reason_size_totals[item.issue] += byte_size
                    self.folder_size_totals[(item.issue, folder_key)] += byte_size

            for issue in sorted(self.reason_items, key=str.casefold):
                items = sorted(self.reason_items[issue], key=lambda bad: str(bad.file).casefold())
                self.reason_items[issue] = items
                expanded = expanded_reasons.get(issue, True) if preserve_selection else True
                header = self.create_reason_header(issue, items, expanded=expanded)
                self.tree.addTopLevelItem(header)
                self.reason_header_items[issue] = header
                folder_groups = self.reason_folder_items.get(issue, {})
                for folder_key in sorted(folder_groups, key=lambda key: self.bad_folder_label(key).casefold()):
                    folder_items = sorted(folder_groups[folder_key], key=lambda bad: bad.file.name.casefold())
                    folder_groups[folder_key] = folder_items
                    folder_expanded = expanded_folders.get((issue, folder_key), True) if preserve_selection else True
                    folder_header = self.create_folder_header(
                        issue,
                        folder_key,
                        folder_items,
                        expanded=folder_expanded,
                    )
                    header.addChild(folder_header)
                    self.folder_header_items[(issue, folder_key)] = folder_header
                    for bad in folder_items:
                        folder_header.addChild(self.tree_item_for_bad_file(bad))
                    self.update_folder_header_item(folder_header)
                self.update_reason_header_item(header)

            if self.items:
                longest_details = max((len(item.details) for item in self.items), default=0)
                if longest_details:
                    self.pending_details_column_width = (
                        self.tree.fontMetrics().averageCharWidth() * longest_details + 36
                    )
                    self.apply_details_column_width()

            if preserve_selection:
                self.restore_reason_tree_selection(selected_paths, current_path)
                self.tree.verticalScrollBar().setValue(scroll_value)
        finally:
            self.tree.blockSignals(previous_block)
            self.tree.setUpdatesEnabled(previous_updates)
            self.tree.viewport().update()

        if preserve_selection:
            selected_path = self.current_path()
            if selected_path and selected_path.exists():
                self.update_preview()

    def restore_reason_tree_selection(self, selected_paths: List[Path], current_path: Optional[Path]):
        selected = set(selected_paths)
        target = None
        self.tree.clearSelection()
        for item in self.file_items_in_order():
            path = self.item_path(item)
            if path in selected:
                item.setSelected(True)
            if current_path and path == current_path:
                target = item
        if target is None and selected:
            target = next((item for item in self.file_items_in_order() if self.item_path(item) in selected), None)
        if target:
            self.tree.setCurrentItem(target)

    def update_reason_header_item(self, item: Optional[QTreeWidgetItem]):
        if not item or item.data(0, self.ROLE_KIND) != "reason":
            return
        issue = str(item.data(0, self.ROLE_ISSUE) or "")
        text = self.reason_header_text(issue, self.reason_items.get(issue, []), item.isExpanded())
        item.setText(0, text)
        for column in range(self.tree.columnCount()):
            item.setToolTip(column, text)

    def update_folder_header_item(self, item: Optional[QTreeWidgetItem]):
        if not item or item.data(0, self.ROLE_KIND) != "folder_group":
            return
        issue = str(item.data(0, self.ROLE_ISSUE) or "")
        folder_key = str(item.data(0, self.ROLE_FOLDER) or "")
        items = self.reason_folder_items.get(issue, {}).get(folder_key, [])
        text = self.folder_header_text(issue, folder_key, items, item.isExpanded())
        item.setText(0, text)
        for column in range(self.tree.columnCount()):
            item.setToolTip(column, folder_key)

    def toggle_bad_reason_header(self, item: QTreeWidgetItem):
        kind = item.data(0, self.ROLE_KIND)
        if kind in {"reason", "folder_group"}:
            item.setExpanded(not item.isExpanded())
            self.sync_bad_header_expansion(item)

    def sync_bad_header_expansion(self, item: QTreeWidgetItem):
        kind = item.data(0, self.ROLE_KIND)
        if kind == "reason":
            self.update_reason_header_item(item)
        elif kind == "folder_group":
            self.update_folder_header_item(item)

    def paths_for_reason_item(self, item: QTreeWidgetItem) -> List[Path]:
        kind = item.data(0, self.ROLE_KIND)
        issue = str(item.data(0, self.ROLE_ISSUE) or "")
        if kind == "folder_group":
            folder_key = str(item.data(0, self.ROLE_FOLDER) or "")
            source = self.reason_folder_items.get(issue, {}).get(folder_key, [])
        else:
            source = self.reason_items.get(issue, [])
        return [bad.file for bad in source if bad.file.exists()]

    def item_path(self, item: Optional[QTreeWidgetItem]) -> Optional[Path]:
        if not item:
            return None
        if item.data(0, self.ROLE_KIND) != "file":
            return None
        path = item.data(0, self.ROLE_PATH)
        return Path(path) if path else None

    def current_path(self) -> Optional[Path]:
        return self.item_path(self.tree.currentItem())

    def rename_current_item(self):
        item = self.tree.currentItem()
        path = self.item_path(item)
        if not item or not path:
            return
        self.renaming_item = item
        self.renaming_path = path
        self.tree.editItem(item, 0)

    def on_item_changed(self, item: QTreeWidgetItem, column: int):
        if self.rename_suppress:
            return
        if column != 0 or item is not self.renaming_item or self.renaming_path is None:
            return
        original = self.renaming_path
        self.renaming_item = None
        self.renaming_path = None
        new_name = item.text(0).strip()
        if not new_name or "/" in new_name or new_name in {".", ".."} or new_name == original.name:
            self.update_bad_file_row(item, original)
            return
        target = unique_path(original.with_name(new_name)) if original.with_name(new_name).exists() else original.with_name(new_name)
        try:
            original.rename(target)
        except (OSError, ValueError) as exc:
            self.progress_label.setText(f"Rename failed: {exc}")
            self.update_bad_file_row(item, original)
            return
        for bad in self.items:
            if bad.file == original:
                bad.file = target
        for bad_items in self.reason_items.values():
            for bad in bad_items:
                if bad.file == original:
                    bad.file = target
        self.update_bad_file_row(item, target)
        self.progress_label.setText(f"Renamed {original.name}")

    def update_bad_file_row(self, item: QTreeWidgetItem, path: Path):
        self.rename_suppress = True
        try:
            item.setText(0, path.name)
            item.setData(0, self.ROLE_PATH, str(path))
            item.setToolTip(0, str(path))
        finally:
            self.rename_suppress = False

    def selected_paths(self) -> List[Path]:
        paths: List[Path] = []
        seen = set()
        for item in self.tree.selectedItems():
            if item.data(0, self.ROLE_KIND) in {"reason", "folder_group"}:
                for path in self.paths_for_reason_item(item):
                    if path not in seen:
                        paths.append(path)
                        seen.add(path)
                continue
            path = self.item_path(item)
            if path and path not in seen:
                paths.append(path)
                seen.add(path)
        return paths

    def descendant_bad_file_items(
        self,
        item: Optional[QTreeWidgetItem],
        *,
        visible_only: bool = False,
    ) -> List[QTreeWidgetItem]:
        if not item:
            return []
        if self.item_path(item):
            return [item]
        rows: List[QTreeWidgetItem] = []
        if visible_only and not item.isExpanded():
            return rows
        for child_index in range(item.childCount()):
            child = item.child(child_index)
            if self.item_path(child):
                rows.append(child)
            else:
                rows.extend(
                    self.descendant_bad_file_items(
                        child,
                        visible_only=visible_only,
                    )
                )
        return rows

    def first_descendant_bad_file_item(
        self,
        item: Optional[QTreeWidgetItem],
    ) -> Optional[QTreeWidgetItem]:
        rows = self.descendant_bad_file_items(item)
        return rows[0] if rows else None

    def file_items_in_order(self) -> List[QTreeWidgetItem]:
        items: List[QTreeWidgetItem] = []
        for top_index in range(self.tree.topLevelItemCount()):
            header = self.tree.topLevelItem(top_index)
            items.extend(
                self.descendant_bad_file_items(
                    header,
                    visible_only=True,
                )
            )
        return items

    def update_preview(self):
        path = self.current_path()
        if path and path.exists():
            large_open = bool(self.quicklook_dialog and self.quicklook_dialog.isVisible())
            if path != self.debug_last_selected_path:
                self.debug_last_selected_path = path
                current_item = self.tree.currentItem()
                debug_log(
                    "input",
                    "bad-file table row selected",
                    force=True,
                    row_kind=current_item.data(0, self.ROLE_KIND) if current_item else "none",
                    selected_rows=len(self.tree.selectedItems()),
                    media_kind=kind_for_path(path),
                    preview_window_open=large_open,
                )
            if large_open:
                self.bad_preview_timer.stop()
                self.pending_bad_preview_path = None
                self.quicklook_dialog.queue_path(path)
            else:
                self.schedule_bad_preview(path)
        else:
            self.debug_last_selected_path = None
            self.bad_preview_timer.stop()
            self.pending_bad_preview_path = None
            self.preview_panel.reset()

    def schedule_bad_preview(self, path: Path):
        if getattr(self.preview_panel, "current_path", None) == path:
            self.bad_preview_timer.stop()
            self.pending_bad_preview_path = None
            return
        self.pending_bad_preview_path = path
        self.bad_preview_timer.start(240 if self.worker and self.worker.isRunning() else 110)

    def apply_pending_bad_preview(self):
        path = self.pending_bad_preview_path
        self.pending_bad_preview_path = None
        if not path or not path.exists():
            self.preview_panel.reset()
            return
        if self.quicklook_dialog and self.quicklook_dialog.isVisible():
            self.quicklook_dialog.queue_path(path)
            return
        current_item = self.tree.currentItem()
        scanner_meta = None
        if self.item_path(current_item) == path:
            def field(column: int) -> str:
                value = current_item.text(column).strip()
                return "" if value in {"", "--", "-"} else value

            scanner_meta = MediaMeta(
                duration=field(4),
                frame_rate=field(5),
                sample_rate=field(6),
                resolution=field(7),
                bit_rate=field(8),
            )
        self.preview_panel.set_path(
            path,
            scanner_meta,
            probe_media=not self.scan_thread_running(),
        )

    def open_tree_item(self, item: QTreeWidgetItem, _column: int = 0):
        if item.data(0, self.ROLE_KIND) in {"reason", "folder_group"}:
            return
        self.open_path(self.item_path(item))

    def open_current(self):
        self.open_path(self.current_path())

    def open_path(self, path: Optional[Path]):
        if path and path.exists():
            open_file_reusing_finder(path)

    def zoom_current_preview(self, path: Optional[Path] = None):
        toggle = path is None
        if path is None:
            current_item = self.tree.currentItem()
            path = self.current_path()
            if (
                path is None
                and current_item is not None
                and current_item.data(0, self.ROLE_KIND) in {"reason", "folder_group"}
            ):
                first_child = self.first_descendant_bad_file_item(current_item)
                path = self.item_path(first_child)
        if not path or not path.exists():
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
                "bad-file preview window closing from Space",
                force=True,
            )
            self.quicklook_dialog.close()
            return
        self.tree.preview_navigation_active = True
        created = self.quicklook_dialog is None
        if created:
            self.quicklook_dialog = LargePreviewDialog(
                self,
                self.open_adjacent_file,
                self.move_selected_to_trash,
                None,
                self.current_path,
                embedded_preview_panel=self.preview_panel,
            )
        self.quicklook_dialog.set_path(path)
        self.quicklook_dialog.show()
        self.quicklook_dialog.raise_()
        self.quicklook_dialog.activateWindow()
        self.preview_panel.pause_video_preview()
        debug_log(
            "response",
            "separate preview window opened",
            force=True,
            context="bad-file scan",
            created=created,
            media_kind=kind_for_path(path),
            width=self.quicklook_dialog.width(),
            height=self.quicklook_dialog.height(),
        )

    def clear_bad_file_selection(self):
        self.bad_preview_timer.stop()
        self.pending_bad_preview_path = None
        self.preview_panel.reset()
        if self.quicklook_dialog and self.quicklook_dialog.isVisible():
            self.quicklook_dialog.close()

    def open_adjacent_file(self, direction: int, video_only: bool = False) -> bool:
        rows = self.file_items_in_order()
        if video_only:
            rows = [
                row for row in rows
                if (path := self.item_path(row)) is not None and is_video_path(path)
            ]
        if not rows:
            return False
        current = self.tree.currentItem()
        try:
            index = rows.index(current)
        except ValueError:
            current_path = self.current_path()
            index = next((i for i, row in enumerate(rows) if self.item_path(row) == current_path), 0)
        next_index = index + direction
        if next_index < 0 or next_index >= len(rows):
            return False
        target = rows[next_index]
        self.tree.clearSelection()
        target.setSelected(True)
        self.tree.setCurrentItem(target)
        self.tree.scrollToItem(target)
        path = self.item_path(target)
        if path:
            if self.quicklook_dialog and self.quicklook_dialog.isVisible():
                self.quicklook_dialog.queue_path(path)
            else:
                self.schedule_bad_preview(path)
            return True
        return False

    def open_context_menu(self, position):
        item = self.tree.itemAt(position)
        if not item:
            return
        if not item.isSelected():
            self.tree.clearSelection()
            item.setSelected(True)
            self.tree.setCurrentItem(item)
        path = self.item_path(item)
        menu = QMenu(self)
        group_kind = item.data(0, self.ROLE_KIND)
        if group_kind in {"reason", "folder_group"}:
            preview_action = menu.addAction("Preview First File")
            reveal_action = None
            open_action = None
            menu.addSeparator()
            delete_action = menu.addAction(
                "Move Folder Group to Trash"
                if group_kind == "folder_group"
                else "Move Reason Group to Trash"
            )
        else:
            open_action = menu.addAction("Open")
            preview_action = menu.addAction("Preview")
            reveal_action = menu.addAction("Reveal in Finder")
            menu.addSeparator()
            delete_action = menu.addAction("Move Selected to Trash")
        chosen = menu.exec(self.tree.viewport().mapToGlobal(position))
        if open_action is not None and chosen == open_action:
            self.open_path(path)
        elif preview_action is not None and chosen == preview_action:
            preview_path = path
            if preview_path is None:
                preview_path = self.item_path(self.first_descendant_bad_file_item(item))
            self.zoom_current_preview(preview_path)
        elif reveal_action is not None and chosen == reveal_action and path:
            reveal_in_finder(path)
        elif chosen == delete_action:
            self.move_selected_to_trash()

    def remember_deleted_bad_files(self, paths: List[Path]):
        path_set = set(paths)
        for item in list(self.items):
            if item.file in path_set:
                self.deleted_bad_items_by_path[item.file].append(item)

    def move_selected_to_trash(self):
        paths = self.selected_paths()
        if not paths:
            return
        paths = list(dict.fromkeys(paths))
        before = [self.item_path(item) for item in self.file_items_in_order()]
        indexes = [before.index(path) for path in paths if path in before]
        fallback_index = max(0, min(indexes) - 1) if indexes else 0
        preferred_path = None
        for candidate in reversed(before[: min(indexes) if indexes else 0]):
            if candidate and candidate.exists() and candidate not in paths:
                preferred_path = candidate
                break
        self.remember_deleted_bad_files(paths)
        worker = self.worker
        if worker is not None:
            try:
                if worker.isRunning():
                    worker.allow_paths_removed(paths)
            except RuntimeError:
                pass
        self.suppressed_paths.update(paths)
        self.remove_bad_paths_from_model(paths)
        self.remove_bad_paths_from_tree(paths)
        self.select_bad_file_after_remove(fallback_index, preferred_path)
        self.start_background_trash_move(paths)

    def remove_bad_paths_from_model(self, paths: List[Path]):
        path_set = set(paths)
        self.items = [item for item in self.items if item.file not in path_set]
        self.bad_item_keys = {(str(item.file), item.issue) for item in self.items}
        self.rebuild_reason_indexes()

    def remove_bad_paths_from_tree(self, paths: List[Path]):
        path_set = set(paths)
        previous_block = self.tree.blockSignals(True)
        previous_updates = self.tree.updatesEnabled()
        self.tree.setUpdatesEnabled(False)
        try:
            for top_index in range(self.tree.topLevelItemCount() - 1, -1, -1):
                reason_header = self.tree.topLevelItem(top_index)
                issue = str(reason_header.data(0, self.ROLE_ISSUE) or "")
                for folder_index in range(reason_header.childCount() - 1, -1, -1):
                    folder_header = reason_header.child(folder_index)
                    folder_key = str(folder_header.data(0, self.ROLE_FOLDER) or "")
                    for file_index in range(folder_header.childCount() - 1, -1, -1):
                        file_item = folder_header.child(file_index)
                        if self.item_path(file_item) in path_set:
                            folder_header.takeChild(file_index)
                    if folder_header.childCount() == 0:
                        reason_header.takeChild(folder_index)
                        self.folder_header_items.pop((issue, folder_key), None)
                    else:
                        self.update_folder_header_item(folder_header)
                if reason_header.childCount() == 0:
                    self.tree.takeTopLevelItem(top_index)
                    self.reason_header_items.pop(issue, None)
                else:
                    self.update_reason_header_item(reason_header)
        finally:
            self.tree.blockSignals(previous_block)
            self.tree.setUpdatesEnabled(previous_updates)
            self.tree.viewport().update()

    def select_bad_file_after_remove(self, select_index: int = 0, select_path: Optional[Path] = None):
        items = self.file_items_in_order()
        if not items:
            self.tree.clearSelection()
            self.preview_panel.reset()
            if self.quicklook_dialog and self.quicklook_dialog.isVisible():
                self.quicklook_dialog.close()
            return
        target = None
        if select_path is not None:
            target = next((item for item in items if self.item_path(item) == select_path), None)
        if target is None:
            target = items[max(0, min(select_index, len(items) - 1))]
        self.tree.clearSelection()
        target.setSelected(True)
        self.tree.setCurrentItem(target)
        self.tree.scrollToItem(target)
        self.update_preview()

    def on_background_trash_finished(self, worker: TrashMoveWorker, moves: List[TrashMove], failures: List[Path]):
        if moves:
            self.undo_stack.append(TrashAction(moves))
            self.redo_stack.clear()
            self.update_undo_button()
        if failures:
            existing = {(item.file, item.issue) for item in self.items}
            for path in failures:
                self.suppressed_paths.discard(path)
                for item in self.deleted_bad_items_by_path.pop(path, []):
                    item.file = path
                    key = (path, item.issue)
                    if key not in existing:
                        self.items.append(item)
                        existing.add(key)
            self.progress_label.setText(
                f"Moved {human_count(len(moves))}; {human_count(len(failures))} failed"
            )
            self.rebuild_existing_rows()
        else:
            self.progress_label.setText(f"Moved {human_count(len(moves))} file(s) to Trash")

    def rebuild_existing_rows(self, select_index: int = 0, select_path: Optional[Path] = None):
        existing = [item for item in self.items if item.file.exists()]
        self.items = existing
        self.populate_reason_tree()
        items = self.file_items_in_order()
        if items:
            target = None
            if select_path is not None:
                target = next((item for item in items if self.item_path(item) == select_path), None)
            if target is None:
                target = items[min(select_index, len(items) - 1)]
            self.tree.clearSelection()
            target.setSelected(True)
            self.tree.setCurrentItem(target)
            self.tree.scrollToItem(target)
            self.update_preview()

    def undo_trash(self):
        if not self.undo_stack:
            return
        action = self.undo_stack.pop()
        restored_moves: List[TrashMove] = []
        remaining_moves: List[TrashMove] = []
        restored_items: List[BadFileItem] = []
        for move in action.moves:
            if not move.trash.exists():
                remaining_moves.append(move)
                continue
            target = unique_path(move.original) if move.original.exists() else move.original
            try:
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.move(str(move.trash), str(target))
                move.restored = target
                for item in self.deleted_bad_items_by_path.pop(move.original, []):
                    item.file = target
                    restored_items.append(item)
                self.suppressed_paths.discard(move.original)
                self.suppressed_paths.discard(target)
                restored_moves.append(move)
            except OSError:
                remaining_moves.append(move)
        if restored_moves:
            existing = {(item.file, item.issue) for item in self.items}
            for item in restored_items:
                key = (item.file, item.issue)
                if key not in existing:
                    self.items.append(item)
                    existing.add(key)
            self.redo_stack.append(TrashAction(restored_moves))
            self.progress_label.setText(f"Restored {human_count(len(restored_moves))} file(s)")
            first_move = restored_moves[0]
            self.rebuild_existing_rows(select_path=first_move.restored or first_move.original)
        if remaining_moves:
            self.undo_stack.append(TrashAction(remaining_moves))
        self.update_undo_button()

    def redo_trash(self):
        if not self.redo_stack:
            return
        action = self.redo_stack.pop()
        moved_moves: List[TrashMove] = []
        remaining_moves: List[TrashMove] = []
        for move in action.moves:
            source = move.restored or move.original
            if not source.exists():
                remaining_moves.append(move)
                continue
            source_items = [item for item in self.items if item.file == source]
            new_move = move_to_trash_recorded(source)
            if new_move:
                stored = self.deleted_bad_items_by_path[move.original]
                stored_ids = {id(item) for item in stored}
                stored.extend(item for item in source_items if id(item) not in stored_ids)
                self.suppressed_paths.add(move.original)
                move.trash = new_move.trash
                move.restored = None
                moved_moves.append(move)
            else:
                remaining_moves.append(move)
        if moved_moves:
            self.undo_stack.append(TrashAction(moved_moves))
            self.update_undo_button()
            self.progress_label.setText(f"Moved {human_count(len(moved_moves))} file(s) back to Trash")
            self.rebuild_existing_rows()
        if remaining_moves:
            self.redo_stack.append(TrashAction(remaining_moves))

    def closeEvent(self, event):
        debug_window_close_context(self, "scanner")
        if self.scan_thread_running() or self.trash_thread_running():
            self.close_after_scan_stops = True
            if self.worker and self.worker.isRunning():
                self.stop_scan()
            self.stop_background_trash_moves()
            self.progress_label.setText("Finishing active file work before closing")
            event.ignore()
            return
        if defer_close_until_windowed(self, event, "bad_file_scan"):
            return
        save_window_geometry(self, "bad_file_scan")
        save_tree_header_state(self.tree, "bad_files_v3")
        if self.quicklook_dialog and self.quicklook_dialog.isVisible():
            self.quicklook_dialog.close()
        self.preview_panel.stop_preview_workers()
        super().closeEvent(event)

    def resizeEvent(self, event):
        super().resizeEvent(event)
        schedule_settled_window_geometry_remember(self)

    def moveEvent(self, event):
        super().moveEvent(event)
        schedule_settled_window_geometry_remember(self)

    def showEvent(self, event):
        super().showEvent(event)
        temporarily_attach_window_to_owner_space(self, self.owner_window)
        schedule_macos_native_fullscreen_button(self)

    def changeEvent(self, event):
        track_standard_fullscreen_change(self, event, "bad_file_scan")
        if promote_macos_zoom_to_fullscreen(
            self,
            event,
            before_promote=lambda: capture_standard_window_geometry(
                self,
                "bad_file_scan",
            ),
        ):
            event.accept()
            return
        super().changeEvent(event)
