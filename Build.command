#!/bin/zsh

# Double-click this file in Finder to build Folder Manager.app and its DMG.
# The launcher resolves every path from its own location, so it also works from
# any terminal directory. Set BUILD_NO_PAUSE=1 for non-interactive automation.
emulate -L zsh
setopt NO_UNSET PIPE_FAIL

export PATH="/opt/homebrew/bin:/usr/local/bin:/opt/local/bin:${PATH:-/usr/bin:/bin}"

readonly launcher_path="${0:A}"
readonly app_dir="${launcher_path:h}"
readonly programs_dir="${app_dir:h:h}"
readonly source_path="$app_dir/Folder_Manager.py"
readonly icon_source="$app_dir/Folder_Manager.icns"
readonly shared_source="$programs_dir/Z_Shared_Tools/shared_media_tools.py"
readonly build_log_dir="$app_dir/.build-logs"

if [[ "${BUILD_DRY_RUN:-0}" == "1" ]]; then
  print "Folder Manager build launcher is ready."
  print "  App folder: $app_dir"
  print "  Shared tools: $shared_source"
  exit 0
fi

mkdir -p -- "$build_log_dir"
readonly build_log="$build_log_dir/Build-$(date +%Y%m%d-%H%M%S)-$$.log"

run_build() (
set -euo pipefail
setopt NULL_GLOB

generated_spec="$app_dir/.Folder Manager.generated.$$.spec"
bundle_path="$app_dir/dist/Folder Manager.app"
dmg_path="$app_dir/Folder Manager.dmg"
pyinstaller_config="$app_dir/.pyinstaller-config-build"
tmp_root="${TMPDIR:-/tmp}"
tmp_root="${tmp_root%/}"
build_completed=0
dmg_is_mounted=0
dmg_workspace=""
dmg_payload=""
dmg_mount=""
dmg_next=""

[[ -f "$source_path" ]]
[[ -f "$icon_source" ]]
[[ -f "$shared_source" ]]
[[ "$tmp_root" == /* && -d "$tmp_root" ]]
[[ ! -e "$dmg_path" || -f "$dmg_path" ]]

# Remove only the explicitly recognized generated paths inside this app
# directory. Source files, install-backups, and the current generic DMG are
# deliberately outside this allowlist.
remove_generated_path() {
  local target="$1"

  case "$target" in
    "$app_dir/build"|\
    "$app_dir/dist"|\
    "$app_dir/dist/Folder Manager"|\
    "$app_dir/__pycache__"|\
    "$app_dir"/.Folder\ Manager.generated.*.spec|\
    "$app_dir/.pyinstaller-config"|\
    "$app_dir"/.pyinstaller-config-*|\
    "$app_dir"/.Folder\ Manager.next.*.dmg)
      if [[ -e "$target" || -L "$target" ]]; then
        # Finder can recreate .DS_Store between rm's directory scan and its
        # final rmdir. Retry the same allow-listed target so a double-clicked
        # build is not defeated by that harmless metadata race.
        local cleanup_attempt
        for cleanup_attempt in 1 2 3; do
          /bin/rm -rf -- "$target" 2>/dev/null || true
          [[ ! -e "$target" && ! -L "$target" ]] && return 0
          sleep 0.1
        done
        /bin/rm -rf -- "$target"
      fi
      ;;
    *)
      print -u2 "Refusing to remove an unexpected path: $target"
      return 1
      ;;
  esac
}

cleanup_on_exit() {
  local exit_status=$?
  set +e

  if (( dmg_is_mounted )) && [[ -n "$dmg_mount" ]]; then
    hdiutil detach "$dmg_mount" >/dev/null 2>&1 || true
  fi
  if [[ -n "$dmg_next" ]]; then
    remove_generated_path "$dmg_next" >/dev/null 2>&1 || true
  fi
  if [[ -n "$dmg_workspace" && "$dmg_workspace" == "$tmp_root"/folder-manager-dmg.* ]]; then
    rm -rf -- "$dmg_workspace"
  fi

  remove_generated_path "$app_dir/build" >/dev/null 2>&1 || true
  remove_generated_path "$app_dir/__pycache__" >/dev/null 2>&1 || true
  remove_generated_path "$generated_spec" >/dev/null 2>&1 || true
  remove_generated_path "$pyinstaller_config" >/dev/null 2>&1 || true
  if (( ! build_completed )); then
    remove_generated_path "$app_dir/dist" >/dev/null 2>&1 || true
  fi

  return "$exit_status"
}
trap cleanup_on_exit EXIT
trap 'exit 130' INT TERM

print "Cleaning old Folder Manager build artifacts..."
remove_generated_path "$app_dir/build"
remove_generated_path "$app_dir/dist"
remove_generated_path "$app_dir/__pycache__"
for stale_path in \
  "$app_dir"/.Folder\ Manager.next.*.dmg(N) \
  "$app_dir"/.Folder\ Manager.generated.*.spec(N) \
  "$app_dir"/.pyinstaller-config(N) \
  "$app_dir"/.pyinstaller-config-*(N); do
  remove_generated_path "$stale_path"
done

mkdir -p -- "$pyinstaller_config"
export PYINSTALLER_CONFIG_DIR="$pyinstaller_config"
cd "$app_dir"

bootstrap_python=""
for candidate in python3.12 python3.11 python3; do
  if command -v "$candidate" >/dev/null 2>&1 && "$candidate" - <<'PY' >/dev/null 2>&1
import sys
raise SystemExit(0 if sys.version_info >= (3, 11) else 1)
PY
  then
    bootstrap_python="$(command -v "$candidate")"
    break
  fi
done
if [[ -z "$bootstrap_python" ]]; then
  print -u2 "Folder Manager requires Python 3.11 or newer for release builds."
  exit 1
fi

venv_dir="$app_dir/.build-venv"
venv_origin_file="$venv_dir/.build-origin"
bootstrap_version="$($bootstrap_python -c 'import sys; print(f"{sys.version_info.major}.{sys.version_info.minor}")')"
expected_venv_origin="$app_dir|$bootstrap_python|$bootstrap_version"
current_venv_origin=""
[[ -f "$venv_origin_file" ]] && current_venv_origin="$(<"$venv_origin_file")"
if [[ ! -x "$venv_dir/bin/python" || "$current_venv_origin" != "$expected_venv_origin" ]]; then
  print "Creating a fresh private build environment: $venv_dir"
  if [[ -d "$venv_dir" ]]; then
    "$bootstrap_python" -m venv --clear "$venv_dir"
  else
    "$bootstrap_python" -m venv "$venv_dir"
  fi
  print -r -- "$expected_venv_origin" > "$venv_origin_file"
fi
build_python="$venv_dir/bin/python"
print "Building with: $($build_python --version) at $build_python"

"$build_python" -m pip install -U pip
"$build_python" -m pip install -U \
  pyinstaller \
  pyinstaller-hooks-contrib \
  PySide6 \
  pyobjc-framework-Cocoa \
  pillow \
  "numpy<2"

missing_helpers=()
for tool in ffmpeg ffprobe; do
  if command -v "$tool" >/dev/null 2>&1; then
    print "Bundling $tool from: $(command -v "$tool")"
  else
    missing_helpers+=("$tool")
  fi
done
if (( ${#missing_helpers[@]} )); then
  print -u2 "Release build refused: missing required helper(s): ${missing_helpers[*]}"
  print -u2 "On macOS, install them with: brew install ffmpeg"
  exit 1
fi

# Keep the release recipe inside this one build file. The temporary spec is
# generated only for PyInstaller and is removed by cleanup_on_exit.
cat > "$generated_spec" <<'PYINSTALLER_SPEC'
# -*- mode: python ; coding: utf-8 -*-

import ast
import os
import shutil
from pathlib import Path


def string_constant(source_path, constant_name):
    tree = ast.parse(source_path.read_text(encoding="utf-8"), filename=str(source_path))
    for node in tree.body:
        if isinstance(node, (ast.Assign, ast.AnnAssign)):
            targets = node.targets if isinstance(node, ast.Assign) else [node.target]
            if any(isinstance(target, ast.Name) and target.id == constant_name for target in targets):
                value = ast.literal_eval(node.value)
                if isinstance(value, str) and value:
                    return value
    raise ValueError(f"{constant_name} was not found in {source_path}")


def first_existing(paths):
    for path in paths:
        if path and path.is_file():
            return path.resolve()
    return None


def helper_binary(name):
    override = os.environ.get(f"{name.upper()}_BINARY")
    candidates = [
        Path(override).expanduser() if override else None,
        Path(found).expanduser() if (found := shutil.which(name)) else None,
        Path("/opt/homebrew/bin") / name,
        Path("/usr/local/bin") / name,
        Path("/opt/local/bin") / name,
    ]
    return first_existing(candidates)


app_dir = Path(SPECPATH).resolve()
programs_dir = app_dir.parents[1]
entry_script = app_dir / "Folder_Manager.py"
shared_dir = programs_dir / "Z_Shared_Tools"
shared_module = shared_dir / "shared_media_tools.py"

source_version = string_constant(shared_module, "APP_VERSION")
release_version = source_version[1:] if source_version[:1].lower() == "v" else source_version
icon_path = first_existing([app_dir / "Folder_Manager.icns"])
icon = str(icon_path) if icon_path else None

binaries = []
for tool_name in ("ffmpeg", "ffprobe"):
    tool_path = helper_binary(tool_name)
    if tool_path:
        binaries.append((str(tool_path), "."))

datas = [(str(shared_module), ".")]
hiddenimports = [
    "shared_media_tools",
    "AppKit",
    "Foundation",
    "objc",
    "PIL",
    "PIL.Image",
    "PIL.ImageOps",
    "PIL.ImageStat",
    "PySide6.QtMultimedia",
    "PySide6.QtMultimediaWidgets",
    "PySide6.QtPdf",
    "numpy",
]

a = Analysis(
    [str(entry_script)],
    pathex=[str(shared_dir), str(programs_dir), str(app_dir)],
    binaries=binaries,
    datas=datas,
    hiddenimports=hiddenimports,
    hookspath=[],
    hooksconfig={},
    runtime_hooks=[],
    excludes=["imagehash", "imageio_ffmpeg", "matplotlib", "pywt", "scipy"],
    noarchive=False,
    optimize=0,
)
pyz = PYZ(a.pure)
exe = EXE(
    pyz,
    a.scripts,
    [],
    exclude_binaries=True,
    name="Folder Manager",
    debug=False,
    bootloader_ignore_signals=False,
    strip=False,
    upx=True,
    console=False,
    disable_windowed_traceback=False,
    argv_emulation=False,
    target_arch=None,
    codesign_identity=None,
    entitlements_file=None,
    icon=[icon] if icon else None,
)
coll = COLLECT(
    exe,
    a.binaries,
    a.datas,
    strip=False,
    upx=True,
    upx_exclude=[],
    name="Folder Manager",
)
app = BUNDLE(
    coll,
    name="Folder Manager.app",
    icon=icon,
    bundle_identifier="com.boyuan.foldermanager",
    version=release_version,
    info_plist={
        "CFBundleDisplayName": "Folder Manager",
        "CFBundleName": "Folder Manager",
        "CFBundleShortVersionString": release_version,
        "CFBundleVersion": release_version,
        "NSHighResolutionCapable": True,
    },
)
PYINSTALLER_SPEC

# FFMPEG_BINARY and FFPROBE_BINARY may point the generated recipe at explicit
# non-PATH copies.
"$build_python" -m PyInstaller --noconfirm --clean "$generated_spec"

[[ -d "$bundle_path" ]]
[[ -f "$bundle_path/Contents/Info.plist" ]]
[[ -f "$bundle_path/Contents/Resources/shared_media_tools.py" ]]
codesign --verify --deep --strict "$bundle_path"
cmp -s "$shared_source" "$bundle_path/Contents/Resources/shared_media_tools.py"

release_version="$(/usr/libexec/PlistBuddy -c 'Print :CFBundleShortVersionString' "$bundle_path/Contents/Info.plist")"
[[ -n "$release_version" ]]
print "Built and verified app: $bundle_path"

# Stage the new installer under a temporary name. The existing generic DMG is
# not touched until this image has mounted, passed signature/version checks,
# and been compared with the app that was just built.
dmg_workspace="$(mktemp -d "$tmp_root/folder-manager-dmg.XXXXXX")"
dmg_payload="$dmg_workspace/payload"
dmg_mount="$dmg_workspace/mount"
dmg_next="$app_dir/.Folder Manager.next.$$.dmg"
mkdir -p -- "$dmg_payload" "$dmg_mount"
ditto "$bundle_path" "$dmg_payload/Folder Manager.app"
ln -s /Applications "$dmg_payload/Applications"
hdiutil create \
  -format UDZO \
  -volname "Folder Manager $release_version" \
  -srcfolder "$dmg_payload" \
  "$dmg_next"
hdiutil verify "$dmg_next"
hdiutil attach -nobrowse -readonly -mountpoint "$dmg_mount" "$dmg_next" >/dev/null
dmg_is_mounted=1

mounted_bundle="$dmg_mount/Folder Manager.app"
mounted_version="$(/usr/libexec/PlistBuddy -c 'Print :CFBundleShortVersionString' "$mounted_bundle/Contents/Info.plist")"
[[ "$mounted_version" == "$release_version" ]]
codesign --verify --deep --strict "$mounted_bundle"
cmp -s \
  "$bundle_path/Contents/Resources/shared_media_tools.py" \
  "$mounted_bundle/Contents/Resources/shared_media_tools.py"

hdiutil detach "$dmg_mount" >/dev/null
dmg_is_mounted=0

# Both paths are on the same filesystem, so this is an atomic replacement of
# the old generic installer after verification succeeds.
mv -f -- "$dmg_next" "$dmg_path"
dmg_next=""

# PyInstaller's COLLECT directory duplicates the completed .app bundle and is
# not a deliverable. Keep only dist/Folder Manager.app and the verified DMG.
remove_generated_path "$app_dir/dist/Folder Manager"
build_completed=1

print "Built and verified DMG: $dmg_path"
print "Done. Current deliverables:"
print "  $bundle_path"
print "  $dmg_path"
)

run_build 2>&1 | tee "$build_log"
typeset -a build_pipeline_status
build_pipeline_status=("${pipestatus[@]}")
build_status="${build_pipeline_status[1]}"
if (( build_status == 0 && build_pipeline_status[2] != 0 )); then
  build_status="${build_pipeline_status[2]}"
fi

typeset -a old_build_logs
old_build_logs=("$build_log_dir"/Build-*.log(N.om))
if (( ${#old_build_logs[@]} > 12 )); then
  rm -f -- "${old_build_logs[@]:12}"
fi

print
if (( build_status == 0 )); then
  print "Build completed successfully."
else
  print -u2 "Build failed with status $build_status."
fi
print "Build log: $build_log"

if [[ -t 0 && "${BUILD_NO_PAUSE:-0}" != "1" ]]; then
  print
  read -r "?Press Return to close this window..."
fi
exit "$build_status"
