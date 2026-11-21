"""Paste Khmer text and generate neural Khmer speech.

Run: python khmer_voice.py
Or double-click run.bat
"""

from __future__ import annotations

import array
import asyncio
import ctypes
import hashlib
import json
import math
import os
import queue
import re
import shutil
import subprocess
import tempfile
import threading
import time
import traceback
import urllib.error
import urllib.parse
import urllib.request
import wave
import tkinter as tk
import tkinter.font as tkfont
from pathlib import Path
from tkinter import messagebox, ttk

import edge_tts

BG = "#161311"
PANEL = "#221c18"
FIELD = "#2a231e"
FG = "#f4efe8"
MUTED = "#b3a396"
GOLD = "#e0a24a"
GOLD_HOVER = "#f0b85e"
DARK_BTN = "#3c332c"
DARK_HOVER = "#4d433b"
STOP = "#8d3b3b"
STOP_HOVER = "#a34a4a"
INK = "#1a120c"

VOICES = (
    ("km-KH-SreymomNeural", "ស្រីមុំ  ·  ស្រី"),
    ("km-KH-PisethNeural", "ពិសិដ្ឋ  ·  ប្រុស"),
)
PITCHES = (
    ("+0Hz", "ធម្មតា"),
    ("-12Hz", "ទាប"),
    ("+8Hz", "ខ្ពស់"),
)
PREVIEW_TEXT = {
    "km-KH-SreymomNeural": "សួស្តី។ ខ្ញុំឈ្មោះស្រីមុំ។ ខ្ញុំនឹងអានរឿងនេះឱ្យអ្នកស្ដាប់។",
    "km-KH-PisethNeural": "សួស្តី។ ខ្ញុំឈ្មោះពិសិដ្ឋ។ ខ្ញុំនឹងអានរឿងនេះឱ្យអ្នកស្ដាប់។",
}
PLACEHOLDER = "បិទភ្ជាប់រឿង ឬអត្ថបទខ្មែរនៅទីនេះ បន្ទាប់មកចុច «បង្កើតសំឡេង»។"
MAX_CHARS = 1000
NAV_KEYS = {
    "Left",
    "Right",
    "Up",
    "Down",
    "Next",
    "Prior",
    "Home",
    "End",
    "Shift_L",
    "Shift_R",
    "Control_L",
    "Control_R",
    "Alt_L",
    "Alt_R",
}

STATE_DIR = Path(os.environ.get("LOCALAPPDATA", tempfile.gettempdir())) / "NITEAN"
TEXT_PATH = STATE_DIR / "last_story.txt"
SETTINGS_PATH = STATE_DIR / "settings.json"
CACHE_MP3 = STATE_DIR / "last_voice.mp3"
CACHE_KEY = STATE_DIR / "last_voice.key"
CUES_PATH = STATE_DIR / "last_voice.cues.json"
SCENE_CACHE = STATE_DIR / "scene-cache"
BED_PATH = STATE_DIR / "horror_bed_v1.wav"
FRAMES_SCRIPT = Path(__file__).with_name("story_frames.ps1")
NO_WINDOW = getattr(subprocess, "CREATE_NO_WINDOW", 0)
WORK_DIR = Path(tempfile.gettempdir()) / "nitean-khmer-voice"
_BED_LOCK = threading.Lock()


class GenerationCancelled(Exception):
    pass


class MciPlayer:
    """Play MP3 files through the Windows MCI interface."""

    def __init__(self) -> None:
        self.winmm = ctypes.windll.winmm
        self.alias = "niteanvoice"
        self.bed_alias = "niteanbed"
        self.opened = False
        self.bed_open = False
        self.path: Path | None = None
        self.bed_path: Path | None = None

    def _send(self, command: str) -> str:
        buffer = ctypes.create_unicode_buffer(512)
        error = self.winmm.mciSendStringW(command, buffer, 511, None)
        if error:
            message = ctypes.create_unicode_buffer(512)
            self.winmm.mciGetErrorStringW(error, message, 511)
            raise RuntimeError(message.value or f"MCI error {error}")
        return buffer.value

    def close(self) -> None:
        if not self.opened:
            return
        try:
            self._send(f"close {self.alias}")
        except RuntimeError:
            pass
        self.opened = False
        self.path = None

    def load(self, path: Path) -> None:
        self.close()
        self._send(f'open "{path}" type mpegvideo alias {self.alias}')
        self._send(f"set {self.alias} time format milliseconds")
        self.opened = True
        self.path = path

    def play(self) -> None:
        if self.opened and self.mode() == "stopped":
            self._send(f"seek {self.alias} to start")
        self._send(f"play {self.alias}")

    def pause(self) -> None:
        self._send(f"pause {self.alias}")

    def resume(self) -> None:
        self._send(f"resume {self.alias}")

    def stop(self) -> None:
        if not self.opened:
            return
        try:
            self._send(f"stop {self.alias}")
            self._send(f"seek {self.alias} to start")
        except RuntimeError:
            self.close()

    def mode(self) -> str:
        if not self.opened:
            return ""
        try:
            return self._send(f"status {self.alias} mode").strip().lower()
        except RuntimeError:
            return ""

    def position(self) -> int:
        if not self.opened:
            return 0
        try:
            return int(self._send(f"status {self.alias} position") or 0)
        except (RuntimeError, ValueError):
            return 0

    def length(self) -> int:
        if not self.opened:
            return 0
        try:
            return int(self._send(f"status {self.alias} length") or 0)
        except (RuntimeError, ValueError):
            return 0

    def close_bed(self) -> None:
        if not self.bed_open:
            return
        try:
            self._send(f"close {self.bed_alias}")
        except RuntimeError:
            pass
        self.bed_open = False
        self.bed_path = None

    def set_bed_volume(self, volume: int) -> None:
        if not self.bed_open:
            return
        level = max(0, min(1000, int(volume) * 10))
        try:
            self._send(f"setaudio {self.bed_alias} volume to {level}")
        except RuntimeError:
            return

    def start_bed(self, path: Path, volume: int) -> None:
        if not self.bed_open or self.bed_path != path:
            self.close_bed()
            self._send(f'open "{path}" type waveaudio alias {self.bed_alias}')
            self.bed_open = True
            self.bed_path = path
        self.set_bed_volume(volume)
        mode = self.bed_mode()
        if mode == "paused":
            self._send(f"resume {self.bed_alias}")
        elif mode != "playing":
            try:
                self._send(f"seek {self.bed_alias} to start")
            except RuntimeError:
                pass
            try:
                self._send(f"play {self.bed_alias} repeat")
            except RuntimeError:
                self._send(f"play {self.bed_alias}")

    def bed_mode(self) -> str:
        if not self.bed_open:
            return ""
        try:
            return self._send(f"status {self.bed_alias} mode").strip().lower()
        except RuntimeError:
            return ""

    def pause_bed(self) -> None:
        if not self.bed_open:
            return
        try:
            self._send(f"pause {self.bed_alias}")
        except RuntimeError:
            self.close_bed()

    def stop_bed(self) -> None:
        if not self.bed_open:
            return
        try:
            self._send(f"stop {self.bed_alias}")
            self._send(f"seek {self.bed_alias} to start")
        except RuntimeError:
            self.close_bed()


def choose_font() -> str:
    families = set(tkfont.families())
    for name in ("Leelawadee UI", "Khmer UI", "DaunPenh", "Segoe UI"):
        if name in families:
            return name
    return "Segoe UI"


def format_ms(milliseconds: int) -> str:
    seconds = max(0, int(milliseconds)) // 1000
    minutes, seconds = divmod(seconds, 60)
    hours, minutes = divmod(minutes, 60)
    if hours:
        return f"{hours}:{minutes:02d}:{seconds:02d}"
    return f"{minutes:02d}:{seconds:02d}"


def friendly_error(exc: BaseException) -> str:
    name = type(exc).__name__
    text = str(exc).replace("\n", " ")
    if name in {
        "ClientConnectorError",
        "ClientError",
        "TimeoutError",
        "ServerTimeoutError",
        "ClientOSError",
        "WSServerHandshakeError",
    } or "timed out" in text.lower():
        return "ភ្ជាប់សេវាសំឡេងមិនបាន។ សូមពិនិត្យអ៊ីនធឺណិត រួចព្យាយាមម្ដងទៀត។"
    if "No audio was received" in text:
        return "សេវាសំឡេងមិនបានឆ្លើយ។ សូមព្យាយាមម្ដងទៀត។"
    return "មានបញ្ហា៖ " + text[:180]


def ensure_pause(paragraph: str) -> str:
    if re.search(r"[។?!៕…]$", paragraph) or paragraph.endswith("..."):
        return paragraph
    return paragraph + "។"


def split_long(paragraph: str) -> list[str]:
    parts = re.split(r"(?<=[។?!៕\n])", paragraph)
    chunks: list[str] = []
    buffer = ""
    for part in parts:
        if not part:
            continue
        if len(part) > MAX_CHARS:
            if buffer:
                chunks.append(buffer)
                buffer = ""
            for start in range(0, len(part), MAX_CHARS):
                chunks.append(part[start : start + MAX_CHARS])
            continue
        if len(buffer) + len(part) <= MAX_CHARS:
            buffer += part
        else:
            if buffer:
                chunks.append(buffer)
            buffer = part
    if buffer:
        chunks.append(buffer)
    return chunks


def split_text(text: str) -> list[str]:
    text = text.replace("\r\n", "\n").replace("\r", "\n").strip()
    paragraphs = [part.strip() for part in re.split(r"\n\s*\n", text) if part.strip()]
    if len(paragraphs) <= 1:
        paragraphs = [part.strip() for part in text.split("\n") if part.strip()]

    chunks: list[str] = []
    buffer = ""
    for paragraph in paragraphs:
        paragraph = ensure_pause(paragraph)
        pieces = split_long(paragraph) if len(paragraph) > MAX_CHARS else [paragraph]
        for piece in pieces:
            candidate = piece if not buffer else f"{buffer}\n{piece}"
            if len(candidate) <= MAX_CHARS:
                buffer = candidate
            else:
                if buffer:
                    chunks.append(buffer)
                buffer = piece
    if buffer:
        chunks.append(buffer)
    return chunks


def split_half(text: str) -> tuple[str, str]:
    mid = max(1, len(text) // 2)
    for mark in ("\n", "។", "?", "!", "៕"):
        index = text.rfind(mark, max(0, mid - 160), min(len(text), mid + 160))
        if 20 < index < len(text) - 20:
            return text[: index + 1].strip(), text[index + 1 :].strip()
    return text[:mid].strip(), text[mid:].strip()


def concat_mp3(paths: list[Path], dest: Path) -> None:
    dest.parent.mkdir(parents=True, exist_ok=True)
    temporary = dest.with_suffix(".writing")
    with temporary.open("wb") as output:
        for path in paths:
            output.write(path.read_bytes())
    temporary.replace(dest)


def estimate_label(text: str, rate_percent: int) -> str:
    count = len(text)
    if count == 0:
        return "0 តួអក្សរ"
    speed = max(0.4, 1 + rate_percent / 100)
    minutes = count / (700 * speed)
    if minutes < 1:
        seconds = max(1, round(minutes * 60))
        duration = f"{seconds} វិនាទី"
    else:
        duration = f"{round(minutes)} នាទី"
    return f"{count:,} តួអក្សរ   ·   រយៈពេលប្រហែល {duration}"


def _horror_sample(t: float, seconds: float, noise: float) -> float:
    two_pi = math.tau
    swell = 0.65 + 0.35 * math.sin(two_pi * (2 / seconds) * t)
    ghost = math.sin(math.pi * t / seconds) ** 2
    phase = t % 1.5
    thump = 0.0
    lub = phase - 0.42
    if 0.0 <= lub < 0.18:
        env = math.sin(math.pi * lub / 0.18) ** 2
        thump += env * math.sin(two_pi * 45 * t) * 0.62
    dub = phase - 0.64
    if 0.0 <= dub < 0.11:
        env = math.sin(math.pi * dub / 0.11) ** 2
        thump += env * math.sin(two_pi * 70 * t) * 0.24
    return (
        0.36 * math.sin(two_pi * 55 * t)
        + 0.18 * swell * math.sin(two_pi * 58 * t)
        + 0.08 * math.sin(two_pi * 82.5 * t)
        + 0.06 * math.sin(two_pi * 41 * t)
        + noise * 0.7
        + thump
        + ghost * (0.08 * math.sin(two_pi * 311 * t) + 0.05 * math.sin(two_pi * 329 * t))
    )


def ensure_horror_bed() -> Path:
    """Build a seamless original horror ambience loop and reuse it."""
    with _BED_LOCK:
        if BED_PATH.exists() and BED_PATH.stat().st_size > 100_000:
            return BED_PATH
        STATE_DIR.mkdir(parents=True, exist_ok=True)
        sample_rate = 22050
        seconds = 36.0
        total = int(sample_rate * seconds)
        fade = int(0.45 * sample_rate)
        samples = array.array("f", [0.0]) * total
        noise = 0.0
        seed = 0x5A17C0DE
        for index in range(total):
            seed = (1664525 * seed + 1013904223) & 0xFFFFFFFF
            white = ((seed >> 8) & 0xFFFFFF) / 16777215.0 * 2.0 - 1.0
            noise = noise * 0.94 + white * 0.06
            samples[index] = _horror_sample(index / sample_rate, seconds, noise)

        loop_length = total - fade
        looped = array.array("f", [0.0]) * loop_length
        for index in range(fade):
            weight = index / fade
            looped[index] = samples[index] * weight + samples[total - fade + index] * (1.0 - weight)
        for index in range(fade, loop_length):
            looped[index] = samples[index]
        peak = max((abs(value) for value in looped), default=1.0) or 1.0
        scale = 0.82 / peak
        pcm = array.array(
            "h",
            (max(-32767, min(32767, int(value * scale * 32767))) for value in looped),
        )
        temporary = BED_PATH.with_suffix(".writing.wav")
        with wave.open(str(temporary), "wb") as handle:
            handle.setnchannels(1)
            handle.setsampwidth(2)
            handle.setframerate(sample_rate)
            handle.writeframes(pcm.tobytes())
        temporary.replace(BED_PATH)
        return BED_PATH


def mix_horror_bed(voice: Path, bed: Path, dest: Path, level: float) -> None:
    """Place the horror bed under a voice file for the downloaded MP3."""
    level = max(0.0, min(1.0, level))
    filt = (
        f"[1:a]volume={level:.4f}[bed];"
        "[0:a][bed]amix=inputs=2:duration=first:dropout_transition=0:normalize=0"
    )
    command = [
        "ffmpeg",
        "-y",
        "-hide_banner",
        "-loglevel",
        "error",
        "-i",
        str(voice),
        "-stream_loop",
        "-1",
        "-i",
        str(bed),
        "-filter_complex",
        filt,
        "-shortest",
        "-c:a",
        "libmp3lame",
        "-q:a",
        "4",
        str(dest),
    ]
    result = subprocess.run(
        command,
        capture_output=True,
        creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0),
    )
    if result.returncode != 0 or not dest.exists() or dest.stat().st_size < 128:
        detail = result.stderr.decode("utf-8", "ignore").strip()
        raise RuntimeError(detail[:240] or "លាយភ្លេងខ្មោចមិនបាន")


def media_duration(path: Path) -> float:
    result = subprocess.run(
        [
            "ffprobe",
            "-v",
            "error",
            "-show_entries",
            "format=duration",
            "-of",
            "csv=p=0",
            str(path),
        ],
        capture_output=True,
        text=True,
        creationflags=NO_WINDOW,
    )
    try:
        return max(0.1, float(result.stdout.strip()))
    except ValueError:
        return max(0.1, path.stat().st_size / 6000)


def read_cues(audio: Path) -> list[dict]:
    file = audio.with_suffix(".cues.json")
    if not file.exists():
        return []
    try:
        data = json.loads(file.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return []
    cues = []
    for item in data:
        if not isinstance(item, dict):
            continue
        spoken = str(item.get("text") or "").strip()
        if not spoken:
            continue
        cues.append(
            {
                "start": float(item["start"]),
                "end": float(item["end"]),
                "text": spoken,
            }
        )
    return cues


def write_cues(audio: Path, cues: list[dict]) -> None:
    audio.with_suffix(".cues.json").write_text(
        json.dumps(cues, ensure_ascii=False),
        encoding="utf-8",
    )


def shift_cues(cues: list[dict], offset: float) -> list[dict]:
    return [
        {
            "start": round(float(cue["start"]) + offset, 3),
            "end": round(float(cue["end"]) + offset, 3),
            "text": cue["text"],
        }
        for cue in cues
    ]


def story_display_lines(text: str) -> list[str]:
    text = text.replace("\r\n", "\n").replace("\r", "\n").strip()
    lines: list[str] = []
    for paragraph in re.split(r"\n+", text):
        paragraph = paragraph.strip()
        if not paragraph:
            continue
        pieces = re.split(r"(?<=[។?!៕])\s*", paragraph)
        for piece in pieces:
            piece = piece.strip()
            if piece:
                lines.append(piece)
    return lines


def cues_from_story(text: str, duration: float) -> list[dict]:
    lines = story_display_lines(text)
    if not lines or duration <= 0:
        return []
    weights = [max(1, len(line)) for line in lines]
    total = sum(weights)
    cursor = 0.0
    cues = []
    for line, weight in zip(lines, weights):
        span = max(0.8, duration * weight / total)
        cues.append({"start": cursor, "end": cursor + span, "text": line})
        cursor += span
    if cues[-1]["end"] > 0:
        scale = duration / cues[-1]["end"]
        for cue in cues:
            cue["start"] = round(cue["start"] * scale, 3)
            cue["end"] = round(cue["end"] * scale, 3)
    cues[-1]["end"] = round(duration, 3)
    return cues


def fit_cues(cues: list[dict], duration: float) -> list[dict]:
    if not cues or duration <= 0:
        return []
    end = float(cues[-1]["end"])
    if end < duration * 0.75 or end > duration * 1.35:
        return []
    fitted = [dict(cue) for cue in cues]
    if abs(end - duration) > 0.35 and end > 0:
        scale = duration / end
        for cue in fitted:
            cue["start"] = round(float(cue["start"]) * scale, 3)
            cue["end"] = round(float(cue["end"]) * scale, 3)
    fitted[-1]["end"] = round(duration, 3)
    return fitted


def readable_cues(cues: list[dict]) -> list[dict]:
    merged: list[dict] = []
    for cue in cues:
        text = str(cue["text"]).strip()
        if not text:
            continue
        start = float(cue["start"])
        end = max(start + 0.4, float(cue["end"]))
        if (
            merged
            and slide_style(merged[-1]["text"]) != "title"
            and slide_style(text) != "title"
            and end - float(merged[-1]["start"]) <= 7.5
            and len(merged[-1]["text"]) + len(text) <= 150
        ):
            merged[-1]["text"] = merged[-1]["text"] + "\n" + text
            merged[-1]["end"] = round(end, 3)
            continue
        merged.append({"start": round(start, 3), "end": round(end, 3), "text": text})
    return merged


def slide_style(text: str) -> str:
    first = text.split("\n", 1)[0].strip()
    if first.startswith("ជំពូក") or ("។" not in text and "\n" not in text and len(text) <= 48):
        return "title"
    return "story"


def render_story_frames(slides: list[dict], folder: Path, track=None) -> list[Path]:
    folder.mkdir(parents=True, exist_ok=True)
    payload = {"frameWidth": 1280, "frameHeight": 720, "slides": []}
    paths: list[Path] = []
    for index, slide in enumerate(slides, start=1):
        image = folder / f"frame_{index:04d}.png"
        payload["slides"].append(
            {
                "file": str(image),
                "style": slide_style(slide["text"]),
                "body": slide["text"],
            }
        )
        paths.append(image)
    spec = folder / "frames.json"
    spec.write_bytes(b"\xef\xbb\xbf" + json.dumps(payload, ensure_ascii=False).encode("utf-8"))
    proc = subprocess.Popen(
        [
            "powershell",
            "-NoProfile",
            "-ExecutionPolicy",
            "Bypass",
            "-File",
            str(FRAMES_SCRIPT),
            "-SpecPath",
            str(spec),
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        creationflags=NO_WINDOW,
    )
    if track is not None:
        track(proc)
    try:
        _stdout, err = proc.communicate()
    finally:
        if track is not None:
            track(None)
    if proc.returncode != 0 or any(not path.exists() for path in paths):
        detail = (err or b"").decode("utf-8", "ignore").strip()
        raise RuntimeError(detail[:240] or "គូរអក្សររឿងមិនបាន")
    return paths


def build_story_video(frames: list[Path], durations: list[float], audio: Path, dest: Path) -> subprocess.Popen:
    playlist = dest.with_suffix(".slides.txt")
    lines: list[str] = []
    for frame, duration in zip(frames, durations):
        lines.append(f"file '{frame.resolve().as_posix()}'")
        lines.append(f"duration {max(0.3, duration):.3f}")
    lines.append(f"file '{frames[-1].resolve().as_posix()}'")
    playlist.write_text("\n".join(lines) + "\n", encoding="utf-8")
    command = [
        "ffmpeg",
        "-y",
        "-hide_banner",
        "-loglevel",
        "error",
        "-f",
        "concat",
        "-safe",
        "0",
        "-i",
        str(playlist),
        "-i",
        str(audio),
        "-fps_mode",
        "vfr",
        "-c:v",
        "libx264",
        "-preset",
        "veryfast",
        "-tune",
        "stillimage",
        "-crf",
        "24",
        "-pix_fmt",
        "yuv420p",
        "-c:a",
        "aac",
        "-b:a",
        "160k",
        "-shortest",
        "-movflags",
        "+faststart",
        str(dest),
    ]
    return subprocess.Popen(command, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, creationflags=NO_WINDOW)


SCENE_LOOK = (
    "cinematic photoreal night film still, pitch-black heavy rain, "
    "simple weathered rural Cambodian wooden house raised on tall stilts, "
    "dark thatched roof, wet mud, the only light is one warm oil lamp in a small window, "
    "dark tropical leaves, deep shadows, quiet ghost-story mood, no daylight, no temple, no pagoda"
)
SCENE_AVOID = (
    " ### text, letters, subtitles, caption, watermark, logo, cartoon, anime, "
    "temple roof, pagoda, blurry, deformed, extra limbs"
)
HORDE_API = "https://aihorde.net/api/v2"
HORDE_MODELS = ("Realistic Vision", "Deliberate", "Dreamshaper")


def translate_to_english(text: str) -> str:
    sample = " ".join(text.split())[:350]
    if not sample:
        return ""
    query = urllib.parse.urlencode({"q": sample, "langpair": "km|en"})
    request = urllib.request.Request(
        "https://api.mymemory.translated.net/get?" + query,
        headers={"User-Agent": "nitean"},
    )
    try:
        with urllib.request.urlopen(request, timeout=25) as response:
            data = json.loads(response.read().decode("utf-8"))
    except (OSError, json.JSONDecodeError, urllib.error.URLError, TimeoutError):
        return ""
    translated = str(data.get("responseData", {}).get("translatedText") or "").strip()
    if not translated or translated.upper().startswith("MYMEMORY"):
        return ""
    return translated


def scene_prompt(english: str, opening: bool) -> str:
    moment = english.strip() or "a silent village house at night"
    if opening:
        moment = "wide establishing shot of the story's place, " + moment
    return f"{SCENE_LOOK}, showing this moment with no written words: {moment[:420]}{SCENE_AVOID}"


def story_scenes(story: str, duration: float) -> list[dict]:
    lines = story_display_lines(story) or [story.strip()]
    lines = [line for line in lines if line.strip()]
    if not lines or duration <= 0:
        return []
    count = 4 if len(lines) >= 8 else (2 if len(lines) >= 3 else 1)
    weights = [max(1, len(line)) for line in lines]
    target = sum(weights) / count
    groups: list[list[str]] = []
    bucket: list[str] = []
    filled = 0
    for line, weight in zip(lines, weights):
        bucket.append(line)
        filled += weight
        if filled >= target and len(groups) < count - 1:
            groups.append(bucket)
            bucket = []
            filled = 0
    if bucket:
        groups.append(bucket)
    scenes: list[dict] = []
    cursor = 0.0
    group_weights = [max(1, sum(len(line) for line in group)) for group in groups]
    total = sum(group_weights) or 1
    for index, (group, weight) in enumerate(zip(groups, group_weights)):
        span = duration * weight / total
        scenes.append(
            {
                "start": cursor,
                "end": cursor + span,
                "prompt": scene_prompt(translate_to_english(" ".join(group)), opening=index == 0),
            }
        )
        cursor += span
    scenes[-1]["end"] = duration
    return scenes


def _horde_request(url: str, payload: dict | None = None, method: str | None = None) -> dict:
    data = None if payload is None else json.dumps(payload).encode("utf-8")
    request = urllib.request.Request(
        url,
        data=data,
        method=method,
        headers={
            "Content-Type": "application/json",
            "apikey": "0000000000",
            "Client-Agent": "nitean:1.0:local",
            "User-Agent": "nitean",
        },
    )
    with urllib.request.urlopen(request, timeout=40) as response:
        raw = response.read().decode("utf-8")
    if not raw.strip():
        return {}
    loaded = json.loads(raw)
    return loaded if isinstance(loaded, dict) else {}


def _cancel_horde(job_id: str) -> None:
    try:
        _horde_request(f"{HORDE_API}/generate/status/{job_id}", method="DELETE")
    except (OSError, json.JSONDecodeError, urllib.error.URLError, TimeoutError):
        return


def _horde_once(prompt: str, dest: Path, cancel: threading.Event, model: str) -> None:
    job = _horde_request(
        f"{HORDE_API}/generate/async",
        {
            "prompt": prompt,
            "params": {
                "sampler_name": "k_euler",
                "cfg_scale": 7,
                "width": 768,
                "height": 448,
                "steps": 22,
                "n": 1,
            },
            "nsfw": False,
            "censor_nsfw": True,
            "models": [model],
            "r2": True,
        },
    )
    job_id = str(job.get("id") or "")
    if not job_id:
        raise RuntimeError("បង្កើតរូបភាពមិនបាន")
    deadline = time.time() + 180
    while True:
        if cancel.is_set():
            _cancel_horde(job_id)
            raise GenerationCancelled
        if time.time() > deadline:
            _cancel_horde(job_id)
            raise RuntimeError("រូបភាពចំណាយពេលយូរពេក")
        time.sleep(2.5)
        state = _horde_request(f"{HORDE_API}/generate/check/{job_id}")
        if state.get("faulted"):
            raise RuntimeError("រូបភាពមិនបាន")
        if state.get("done"):
            break
    status = _horde_request(f"{HORDE_API}/generate/status/{job_id}")
    generations = status.get("generations") or []
    if not generations or not isinstance(generations[0], dict):
        raise RuntimeError("រូបភាពមិនបាន")
    image_url = str(generations[0].get("img") or "")
    if not image_url.startswith("http"):
        raise RuntimeError("រូបភាពមិនបាន")
    image_request = urllib.request.Request(image_url, headers={"User-Agent": "nitean"})
    with urllib.request.urlopen(image_request, timeout=60) as response:
        blob = response.read()
    if len(blob) < 2000:
        raise RuntimeError("រូបភាពមិនបាន")
    dest.write_bytes(blob)


def horde_image(prompt: str, dest: Path, cancel: threading.Event) -> None:
    digest = hashlib.sha256(prompt.encode("utf-8")).hexdigest()[:24]
    cached = SCENE_CACHE / f"{digest}.img"
    if cached.exists() and cached.stat().st_size > 2000:
        dest.write_bytes(cached.read_bytes())
        return
    last_error = "បង្កើតរូបភាពមិនបាន"
    for model in HORDE_MODELS:
        if cancel.is_set():
            raise GenerationCancelled
        try:
            _horde_once(prompt, dest, cancel, model)
            SCENE_CACHE.mkdir(parents=True, exist_ok=True)
            cached.write_bytes(dest.read_bytes())
            return
        except GenerationCancelled:
            raise
        except (OSError, json.JSONDecodeError, urllib.error.URLError, TimeoutError, RuntimeError) as exc:
            last_error = str(exc)[:180] or last_error
    raise RuntimeError(last_error)


def fit_scene_frame(src: Path, dest: Path) -> None:
    result = subprocess.run(
        [
            "ffmpeg",
            "-y",
            "-hide_banner",
            "-loglevel",
            "error",
            "-i",
            str(src),
            "-vf",
            "scale=1280:720:force_original_aspect_ratio=increase,crop=1280:720",
            "-frames:v",
            "1",
            str(dest),
        ],
        capture_output=True,
        creationflags=NO_WINDOW,
    )
    if result.returncode != 0 or not dest.exists() or dest.stat().st_size < 1000:
        raise RuntimeError("រៀបរូបភាពមិនបាន")


def render_story_images(scenes: list[dict], folder: Path, cancel: threading.Event, on_status) -> list[Path]:
    folder.mkdir(parents=True, exist_ok=True)
    frames: list[Path] = []
    for index, scene in enumerate(scenes, start=1):
        if cancel.is_set():
            raise GenerationCancelled
        on_status(f"កំពុងបង្កើតរូបភាព {index}/{len(scenes)}...")
        source = folder / f"scene_{index:02d}.src"
        frame = folder / f"scene_{index:02d}.png"
        horde_image(str(scene["prompt"]), source, cancel)
        fit_scene_frame(source, frame)
        frames.append(frame)
    return frames


class KhmerVoiceApp:
    def __init__(self, root: tk.Tk) -> None:
        self.root = root
        self.font_name = choose_font()
        self.player = MciPlayer()
        self.events: queue.Queue[tuple[str, object]] = queue.Queue()
        self.cancel = threading.Event()
        self.busy = False
        self.placeholder = False
        self.was_playing = False
        self.phase = "idle"
        self.ready_path: Path | None = None
        self.ready_key = ""
        self.persist_job: str | None = None
        self.placeholder_job: str | None = None
        self.story_backup = ""
        self.user_cleared = False
        self.closing = False
        self.export_proc: subprocess.Popen | None = None
        self.alive = True

        self.voice = tk.StringVar(value=VOICES[0][0])
        self.pitch = tk.StringVar(value=PITCHES[0][0])
        self.speed = tk.IntVar(value=-5)
        self.music_on = tk.BooleanVar(value=True)
        self.music_volume = tk.IntVar(value=24)
        self._load_settings()

        self.voice_group: list[tuple[str, tk.Button]] = []
        self.pitch_group: list[tuple[str, tk.Button]] = []
        self.locked_buttons: list[tk.Button] = []

        self._build()
        self._load_story()
        self._restore_audio_cache()
        self.refresh_download()
        threading.Thread(target=ensure_horror_bed, daemon=True).start()
        self.root.protocol("WM_DELETE_WINDOW", self.on_close)
        self.root.after(200, self.tick)

    def _build(self) -> None:
        self.root.title("NITEAN  ·  សំឡេង AI ខ្មែរ")
        self.root.configure(bg=BG)
        self.root.minsize(1080, 680)
        self._center(1140, 800)

        outer = tk.Frame(self.root, bg=BG)
        outer.pack(fill="both", expand=True, padx=18, pady=14)
        outer.columnconfigure(0, weight=1)
        outer.rowconfigure(2, weight=1)

        header = tk.Frame(outer, bg=BG)
        header.grid(row=0, column=0, sticky="ew")
        tk.Label(
            header,
            text="NITEAN",
            bg=BG,
            fg=GOLD,
            font=(self.font_name, 11, "bold"),
        ).pack(anchor="w")
        tk.Label(
            header,
            text="សំឡេង AI ខ្មែរ",
            bg=BG,
            fg=FG,
            font=(self.font_name, 22, "bold"),
        ).pack(anchor="w")
        tk.Label(
            header,
            text="បិទភ្ជាប់អត្ថបទខ្មែរ  រួចបង្កើតជាសំឡេងអានរឿង",
            bg=BG,
            fg=MUTED,
            font=(self.font_name, 11),
        ).pack(anchor="w", pady=(2, 0))
        tk.Frame(outer, bg=GOLD, height=2).grid(row=1, column=0, sticky="ew", pady=(10, 8))

        text_bar = tk.Frame(outer, bg=BG)
        text_bar.grid(row=2, column=0, sticky="nsew")
        text_bar.columnconfigure(0, weight=1)
        text_bar.rowconfigure(1, weight=1)

        label_row = tk.Frame(text_bar, bg=BG)
        label_row.grid(row=0, column=0, sticky="ew", pady=(0, 6))
        tk.Label(
            label_row,
            text="Description  ·  អត្ថបទ",
            bg=BG,
            fg=FG,
            font=(self.font_name, 12, "bold"),
        ).pack(side="left")

        self.paste_btn = self._button(label_row, "បិទភ្ជាប់", self.paste_clipboard, DARK_BTN, FG)
        self.clear_btn = self._button(label_row, "សម្អាត", self.clear_text, DARK_BTN, FG)
        self.clear_btn.pack(side="right", padx=(6, 0))
        self.paste_btn.pack(side="right")
        self.locked_buttons.extend((self.paste_btn, self.clear_btn))

        field = tk.Frame(text_bar, bg=FIELD, highlightbackground="#5a4636", highlightthickness=1)
        field.grid(row=1, column=0, sticky="nsew")
        field.rowconfigure(0, weight=1)
        field.columnconfigure(0, weight=1)

        self.text = tk.Text(
            field,
            wrap="word",
            bg=FIELD,
            fg=FG,
            insertbackground=GOLD,
            selectbackground="#8a5a28",
            selectforeground=FG,
            relief="flat",
            padx=12,
            pady=10,
            undo=True,
            maxundo=40,
            font=(self.font_name, 14),
            spacing1=2,
            spacing3=7,
        )
        scroll = tk.Scrollbar(field, command=self.text.yview, bg=PANEL, troughcolor=PANEL)
        self.text.configure(yscrollcommand=scroll.set)
        self.text.grid(row=0, column=0, sticky="nsew")
        scroll.grid(row=0, column=1, sticky="ns")

        self.menu = tk.Menu(self.root, tearoff=0, bg=PANEL, fg=FG, activebackground=GOLD, activeforeground=INK)
        self.menu.add_command(label="បិទភ្ជាប់", command=self.paste_clipboard)
        self.menu.add_command(label="ចម្លង", command=self.copy_text)
        self.menu.add_command(label="កាត់", command=self.cut_text)
        self.menu.add_separator()
        self.menu.add_command(label="ជ្រើសទាំងអស់", command=self.select_all)

        self.text.bind("<Button-3>", self.show_menu)
        self.text.bind("<Control-v>", self.paste_event)
        self.text.bind("<Control-V>", self.paste_event)
        self.text.bind("<Control-a>", self.select_all_event)
        self.text.bind("<Control-A>", self.select_all_event)
        self.text.bind("<Key>", self.on_text_key)
        self.text.bind("<<Modified>>", self.on_modified)
        self.text.bind("<FocusIn>", self.on_focus_in)
        self.text.bind("<FocusOut>", self.on_focus_out)
        self.root.bind("<Control-Return>", lambda _event: self.generate())

        options = tk.Frame(outer, bg=BG)
        options.grid(row=3, column=0, sticky="ew", pady=(10, 0))

        tk.Label(options, text="សំឡេង", bg=BG, fg=MUTED, font=(self.font_name, 11)).pack(side="left")
        for value, label in VOICES:
            button = self._button(
                options,
                label,
                lambda voice=value: self.choose(self.voice, voice, self.voice_group),
                DARK_BTN,
                FG,
                hover=False,
            )
            button.pack(side="left", padx=(8, 0))
            self.voice_group.append((value, button))

        tk.Label(options, text="   កម្ពស់", bg=BG, fg=MUTED, font=(self.font_name, 11)).pack(side="left", padx=(16, 0))
        for value, label in PITCHES:
            button = self._button(
                options,
                label,
                lambda pitch=value: self.choose(self.pitch, pitch, self.pitch_group),
                DARK_BTN,
                FG,
                hover=False,
            )
            button.pack(side="left", padx=(8, 0))
            self.pitch_group.append((value, button))
        self.refresh_group(self.voice, self.voice_group)
        self.refresh_group(self.pitch, self.pitch_group)

        speed_row = tk.Frame(outer, bg=BG)
        speed_row.grid(row=4, column=0, sticky="ew", pady=(8, 0))
        tk.Label(speed_row, text="ល្បឿន", bg=BG, fg=MUTED, font=(self.font_name, 11)).pack(side="left")
        self.speed_label = tk.Label(
            speed_row,
            text=f"{self.speed.get():+d}%",
            bg=BG,
            fg=GOLD,
            font=(self.font_name, 11, "bold"),
            width=6,
            anchor="w",
        )
        self.speed_label.pack(side="left", padx=(8, 0))
        tk.Scale(
            speed_row,
            from_=-30,
            to=30,
            orient="horizontal",
            variable=self.speed,
            showvalue=False,
            resolution=1,
            command=self.on_speed,
            bg=BG,
            fg=FG,
            troughcolor="#3a312b",
            activebackground=GOLD,
            highlightthickness=0,
            bd=0,
            sliderrelief="flat",
            length=320,
        ).pack(side="left", padx=(4, 0))
        tk.Label(
            speed_row,
            text="យឺត                              លឿន",
            bg=BG,
            fg=MUTED,
            font=(self.font_name, 9),
        ).pack(side="left", padx=(6, 0))

        music_row = tk.Frame(outer, bg=BG)
        music_row.grid(row=5, column=0, sticky="ew", pady=(2, 0))
        tk.Checkbutton(
            music_row,
            text="ភ្លេងខ្មោច",
            variable=self.music_on,
            command=self.on_music_toggle,
            bg=BG,
            fg=FG,
            selectcolor="#3a312b",
            activebackground=BG,
            activeforeground=GOLD,
            font=(self.font_name, 11, "bold"),
            highlightthickness=0,
            bd=0,
        ).pack(side="left")
        tk.Label(music_row, text="កម្រិត", bg=BG, fg=MUTED, font=(self.font_name, 11)).pack(side="left", padx=(16, 0))
        self.music_volume_label = tk.Label(
            music_row,
            text=f"{self.music_volume.get()}%",
            bg=BG,
            fg=GOLD,
            font=(self.font_name, 11, "bold"),
            width=5,
            anchor="w",
        )
        self.music_volume_label.pack(side="left", padx=(8, 0))
        tk.Scale(
            music_row,
            from_=0,
            to=100,
            orient="horizontal",
            variable=self.music_volume,
            showvalue=False,
            resolution=1,
            command=self.on_music_volume,
            bg=BG,
            fg=FG,
            troughcolor="#3a312b",
            activebackground=GOLD,
            highlightthickness=0,
            bd=0,
            sliderrelief="flat",
            length=260,
        ).pack(side="left", padx=(4, 0))
        tk.Label(
            music_row,
            text="ស្ងាត់                         ខ្លាំង",
            bg=BG,
            fg=MUTED,
            font=(self.font_name, 9),
        ).pack(side="left", padx=(6, 0))

        self.count_label = tk.Label(
            outer,
            text="0 តួអក្សរ",
            bg=BG,
            fg=MUTED,
            font=(self.font_name, 11),
            anchor="w",
        )
        self.count_label.grid(row=6, column=0, sticky="ew", pady=(8, 0))

        actions = tk.Frame(outer, bg=BG)
        actions.grid(row=7, column=0, sticky="ew", pady=(10, 0))
        self.generate_btn = self._button(actions, "បង្កើតសំឡេង", self.generate, GOLD, INK, primary=True)
        self.play_btn = self._button(actions, "ចាក់", self.play_current, DARK_BTN, FG)
        self.pause_btn = self._button(actions, "ផ្អាក", self.toggle_pause, DARK_BTN, FG)
        self.stop_btn = self._button(actions, "បញ្ឈប់", self.stop_audio, STOP, FG)
        self.download_btn = self._button(
            actions,
            "ទាញយក MP3",
            self.download_mp3,
            DARK_BTN,
            FG,
            hover=False,
        )
        self.video_btn = self._button(
            actions,
            "វីដេអូ MP4",
            self.create_video,
            DARK_BTN,
            FG,
            hover=False,
        )
        self.preview_btn = self._button(actions, "សាកសំឡេង", self.preview_voice, DARK_BTN, FG)
        for button in (
            self.generate_btn,
            self.play_btn,
            self.pause_btn,
            self.stop_btn,
            self.download_btn,
            self.video_btn,
            self.preview_btn,
        ):
            button.pack(side="left", padx=(0, 8))
        self.locked_buttons.extend(
            (self.generate_btn, self.play_btn, self.preview_btn, self.paste_btn, self.clear_btn)
        )
        self.refresh_download()

        style = ttk.Style(self.root)
        style.theme_use("clam")
        style.configure(
            "Gold.Horizontal.TProgressbar",
            troughcolor="#3a312b",
            background=GOLD,
            bordercolor="#3a312b",
            lightcolor=GOLD,
            darkcolor=GOLD,
            thickness=12,
        )
        self.progress = ttk.Progressbar(outer, style="Gold.Horizontal.TProgressbar", mode="determinate")
        self.progress.grid(row=8, column=0, sticky="ew", pady=(12, 0))

        status_row = tk.Frame(outer, bg=BG)
        status_row.grid(row=9, column=0, sticky="ew", pady=(8, 0))
        status_row.columnconfigure(0, weight=1)
        self.status = tk.Label(
            status_row,
            text="រួចរាល់។ បិទភ្ជាប់អត្ថបទ រួចចុច «បង្កើតសំឡេង»។  ត្រូវការអ៊ីនធឺណិត។",
            bg=BG,
            fg=FG,
            font=(self.font_name, 11),
            anchor="w",
        )
        self.status.grid(row=0, column=0, sticky="ew")
        self.time_label = tk.Label(
            status_row,
            text="00:00 / 00:00",
            bg=BG,
            fg=GOLD,
            font=(self.font_name, 11, "bold"),
        )
        self.time_label.grid(row=0, column=1, sticky="e", padx=(12, 0))
        tk.Label(
            outer,
            text="វីដេអូបង្ហាញរូបភាពតាមអត្ថន័យរឿង     ·     ភ្លេងខ្មោចចូលក្នុង MP3 និងវីដេអូ",
            bg=BG,
            fg=MUTED,
            font=(self.font_name, 9),
            anchor="w",
        ).grid(row=10, column=0, sticky="ew", pady=(4, 0))

        self.show_placeholder()

    def _center(self, width: int, height: int) -> None:
        self.root.update_idletasks()
        screen_w = self.root.winfo_screenwidth()
        screen_h = self.root.winfo_screenheight()
        x = max(0, (screen_w - width) // 2)
        y = max(0, (screen_h - height) // 2 - 30)
        self.root.geometry(f"{width}x{height}+{x}+{y}")

    def _button(
        self,
        parent: tk.Widget,
        text: str,
        command,
        background: str,
        foreground: str,
        primary: bool = False,
        hover: bool = True,
    ) -> tk.Button:
        hover_color = GOLD_HOVER if primary else (STOP_HOVER if background == STOP else DARK_HOVER)
        button = tk.Button(
            parent,
            text=text,
            command=command,
            bg=background,
            fg=foreground,
            activebackground=hover_color,
            activeforeground=foreground if not primary else INK,
            relief="flat",
            bd=0,
            padx=14,
            pady=8,
            font=(self.font_name, 11, "bold"),
            cursor="hand2",
            highlightthickness=0,
        )

        if hover:
            def enter(_event, btn=button, color=hover_color) -> None:
                if str(btn["state"]) != "disabled":
                    btn.configure(bg=color)

            def leave(_event, btn=button, color=background) -> None:
                if str(btn["state"]) != "disabled":
                    btn.configure(bg=color)

            button.bind("<Enter>", enter)
            button.bind("<Leave>", leave)
        return button

    def choose(self, variable: tk.StringVar, value: str, group: list[tuple[str, tk.Button]]) -> None:
        if self.busy:
            return
        variable.set(value)
        self.refresh_group(variable, group)
        self.persist_settings()
        self.refresh_download()

    def refresh_group(self, variable: tk.StringVar, group: list[tuple[str, tk.Button]]) -> None:
        current = variable.get()
        for value, button in group:
            selected = value == current
            button.configure(
                bg=GOLD if selected else DARK_BTN,
                fg=INK if selected else FG,
                activebackground=GOLD if selected else DARK_HOVER,
                activeforeground=INK if selected else FG,
            )

    def on_speed(self, _value: str | None = None) -> None:
        self.speed_label.configure(text=f"{self.speed.get():+d}%")
        self.update_count()
        self.persist_settings()
        self.refresh_download()

    def show_placeholder(self) -> None:
        self.placeholder = True
        self.text.configure(fg=MUTED)
        self.text.delete("1.0", "end")
        self.text.insert("1.0", PLACEHOLDER)
        self.text.edit_modified(False)
        self.update_count()

    def hide_placeholder(self) -> None:
        if not self.placeholder:
            return
        self.placeholder = False
        self.text.delete("1.0", "end")
        self.text.configure(fg=FG)

    def story_text(self) -> str:
        if self.placeholder:
            return ""
        return self.text.get("1.0", "end-1c").strip()

    def on_focus_in(self, _event=None) -> None:
        if self.placeholder and not self.busy:
            self.hide_placeholder()

    def on_focus_out(self, _event=None) -> None:
        if self.closing:
            return
        if self.placeholder_job is not None:
            self.root.after_cancel(self.placeholder_job)
        self.placeholder_job = self.root.after(120, self._show_placeholder_if_empty)

    def _show_placeholder_if_empty(self) -> None:
        self.placeholder_job = None
        if self.closing or not self.alive:
            return
        try:
            content = self.text.get("1.0", "end-1c").strip()
        except tk.TclError:
            return
        if not content:
            self.show_placeholder()

    def on_modified(self, _event=None) -> None:
        if not self.text.edit_modified():
            return
        content = self.text.get("1.0", "end-1c")
        self.text.edit_modified(False)
        if self.closing:
            return
        if content == PLACEHOLDER:
            self.placeholder = True
            self.text.configure(fg=MUTED)
            self.update_count()
            self.refresh_download()
            return
        self.placeholder = False
        self.text.configure(fg=FG)
        stripped = content.strip()
        if stripped:
            self.user_cleared = False
            self.story_backup = stripped
        else:
            self.user_cleared = True
            self.story_backup = ""
        self.update_count()
        self.schedule_persist()
        self.refresh_download()

    def on_text_key(self, event: tk.Event) -> str | None:
        if not self.busy:
            return None
        if event.state & 0x4 and event.keysym.lower() in {"c", "a"}:
            return None
        if event.keysym in NAV_KEYS:
            return None
        return "break"

    def update_count(self) -> None:
        if not hasattr(self, "count_label"):
            return
        self.count_label.configure(text=estimate_label(self.story_text(), self.speed.get()))

    def set_status(self, message: str) -> None:
        self.status.configure(text=message)

    def show_menu(self, event: tk.Event) -> str:
        if not self.busy:
            self.menu.tk_popup(event.x_root, event.y_root)
        return "break"

    def paste_event(self, _event=None) -> str:
        self.paste_clipboard()
        return "break"

    def select_all_event(self, _event=None) -> str:
        self.select_all()
        return "break"

    def select_all(self) -> None:
        self.text.tag_add("sel", "1.0", "end-1c")
        self.text.mark_set("insert", "end-1c")
        self.text.see("insert")

    def paste_clipboard(self) -> None:
        if self.busy:
            return
        self.hide_placeholder()
        try:
            clip = self.root.clipboard_get()
        except tk.TclError:
            self.set_status("គ្មានអត្ថបទក្នុង clipboard។")
            if not self.text.get("1.0", "end-1c").strip():
                self.show_placeholder()
            return
        if self.text.tag_ranges("sel"):
            self.text.delete("sel.first", "sel.last")
        self.text.insert("insert", clip)
        self.text.see("insert")
        self.set_status("បានបិទភ្ជាប់អត្ថបទ។ ចុច «បង្កើតសំឡេង» ដើម្បីអាន។")

    def copy_text(self) -> None:
        if self.placeholder:
            return
        try:
            selected = self.text.get("sel.first", "sel.last")
        except tk.TclError:
            selected = self.story_text()
        self.root.clipboard_clear()
        self.root.clipboard_append(selected)

    def cut_text(self) -> None:
        if self.busy or self.placeholder:
            return
        self.copy_text()
        if self.text.tag_ranges("sel"):
            self.text.delete("sel.first", "sel.last")

    def clear_text(self) -> None:
        if self.busy:
            return
        self.user_cleared = True
        self.story_backup = ""
        self.show_placeholder()
        try:
            if TEXT_PATH.exists():
                TEXT_PATH.unlink()
        except OSError:
            pass
        self.set_status("បានសម្អាតអត្ថបទ។")
        self.refresh_download()

    def settings_key(self, text: str) -> str:
        raw = "\n".join(
            [
                text,
                self.voice.get(),
                f"{self.speed.get():+d}%",
                self.pitch.get(),
            ]
        )
        return hashlib.sha256(raw.encode("utf-8")).hexdigest()

    def set_busy(self, busy: bool) -> None:
        self.busy = busy
        state = "disabled" if busy else "normal"
        for button in self.locked_buttons:
            button.configure(state=state)
        self.refresh_download()

    def voice_label(self) -> str:
        for value, label in VOICES:
            if value == self.voice.get():
                return label.split("·")[0].strip()
        return "Khmer"

    def generate(self) -> None:
        self._start_job(self.story_text(), play_after=True, preview=False, save_to=None)

    def preview_voice(self) -> None:
        sample = PREVIEW_TEXT.get(self.voice.get(), PREVIEW_TEXT["km-KH-SreymomNeural"])
        self._start_job(sample, play_after=True, preview=True, save_to=None)

    def play_current(self) -> None:
        if self.busy:
            return
        story = self.story_text()
        if story and self.ready_path and self.ready_path.exists() and self.ready_key == self.settings_key(story):
            self.start_playback(self.ready_path)
            return
        if self.ready_path and self.ready_path.exists() and not story:
            self.start_playback(self.ready_path)
            return
        self.generate()

    def start_playback(self, path: Path) -> None:
        try:
            if not self.player.opened or self.player.path != path:
                self.player.load(path)
            mode = self.player.mode()
            if mode == "playing":
                self.sync_bed()
                return
            if mode == "paused":
                self.player.resume()
            else:
                self.player.play()
            self.sync_bed()
        except Exception as exc:
            self.set_status("មិនអាចចាក់បានទេ។ សូមទាញយក MP3។ " + friendly_error(exc))
            return
        self.phase = "play"
        self.was_playing = True
        length = max(1, self.player.length())
        self.progress.configure(maximum=length, value=self.player.position())
        self.pause_btn.configure(text="ផ្អាក")
        self.set_status(f"កំពុងអានដោយ {self.voice_label()}...")

    def toggle_pause(self) -> None:
        if not self.player.opened:
            return
        mode = self.player.mode()
        try:
            if mode == "playing":
                self.player.pause()
                self.player.pause_bed()
                self.pause_btn.configure(text="បន្ត")
                self.set_status("បានផ្អាក។")
            elif mode == "paused":
                self.player.resume()
                self.sync_bed()
                self.was_playing = True
                self.pause_btn.configure(text="ផ្អាក")
                self.set_status(f"កំពុងអានដោយ {self.voice_label()}...")
        except Exception as exc:
            self.set_status(friendly_error(exc))

    def stop_audio(self) -> None:
        self.cancel.set()
        self.was_playing = False
        self.player.stop()
        self.player.stop_bed()
        export_proc = self.export_proc
        if export_proc is not None and export_proc.poll() is None:
            export_proc.terminate()
        self.pause_btn.configure(text="ផ្អាក")
        if self.player.opened:
            self.time_label.configure(text=f"00:00 / {format_ms(self.player.length())}")
            self.progress.configure(value=0)
        if not self.busy:
            self.phase = "idle"
            self.set_status("បានបញ្ឈប់។")

    def audio_is_ready(self) -> bool:
        return bool(self.ready_path and self.ready_path.exists() and self.ready_path.stat().st_size > 128)

    def paint_export(self, button: tk.Button, ready: bool) -> None:
        state = "normal" if ready else "disabled"
        background = GOLD if ready else "#2c2622"
        foreground = INK if ready else "#6e6258"
        active = GOLD_HOVER if ready else "#2c2622"
        button.configure(
            state=state,
            bg=background,
            fg=foreground,
            activebackground=active,
            activeforeground=foreground,
        )

    def refresh_download(self) -> None:
        if not hasattr(self, "download_btn"):
            return
        ready = (not self.busy) and self.audio_is_ready()
        self.paint_export(self.download_btn, ready)
        story = self.story_text() if hasattr(self, "text") else ""
        video_ready = ready and bool(story) and self.ready_key == self.settings_key(story)
        if hasattr(self, "video_btn"):
            self.paint_export(self.video_btn, video_ready)

    def download_stem(self) -> str:
        title = ""
        for line in self.story_text().splitlines():
            line = line.strip()
            if line:
                title = line
                break
        title = re.sub(r'[<>:"/\\|?*]', "", title).strip(" .")
        return (title or "khmer-voice")[:80]

    def on_music_toggle(self) -> None:
        self.persist_settings()
        if self.player.mode() == "playing":
            self.sync_bed()

    def on_music_volume(self, _value: str | None = None) -> None:
        if hasattr(self, "music_volume_label"):
            self.music_volume_label.configure(text=f"{self.music_volume.get()}%")
        self.persist_settings()
        if self.player.mode() == "playing":
            self.sync_bed()

    def sync_bed(self) -> None:
        if self.player.mode() != "playing":
            return
        if self.music_on.get() and self.music_volume.get() > 0:
            self.start_bed()
        else:
            self.player.stop_bed()

    def start_bed(self) -> None:
        try:
            self.player.start_bed(ensure_horror_bed(), self.music_volume.get())
        except Exception as exc:
            self.player.close_bed()
            self.set_status("សំឡេងកំពុងអាន តែភ្លេងខ្មោចមិនបានចាក់។ " + friendly_error(exc)[:90])

    def download_mp3(self) -> None:
        if self.busy or not self.audio_is_ready():
            self.set_status("សំឡេងមិនទាន់រួចរាល់ទេ។ សូមចុច «បង្កើតសំឡេង» សិន។")
            return
        downloads = Path.home() / "Downloads"
        try:
            downloads.mkdir(parents=True, exist_ok=True)
            destination = downloads / f"{self.download_stem()}.mp3"
            number = 2
            while destination.exists():
                destination = downloads / f"{self.download_stem()} ({number}).mp3"
                number += 1
        except OSError as exc:
            messagebox.showerror("NITEAN", friendly_error(exc))
            return
        with_music = self.music_on.get() and self.music_volume.get() > 0
        if not with_music:
            try:
                self._copy_ready_audio(destination)
            except OSError as exc:
                messagebox.showerror("NITEAN", friendly_error(exc))
                return
            self._reveal_download(destination)
            return
        self.download_btn.configure(state="disabled")
        self.set_status("កំពុងដាក់ភ្លេងខ្មោចក្នុងឯកសារ...")
        threading.Thread(
            target=self._download_with_music,
            args=(destination, self.music_volume.get() / 100),
            daemon=True,
        ).start()

    def _download_with_music(self, destination: Path, level: float) -> None:
        try:
            source = self.ready_path
            if source is None or not source.exists():
                raise OSError("រកឯកសារសំឡេងមិនឃើញ")
            mix_horror_bed(source, ensure_horror_bed(), destination, level)
            self.events.put(("downloaded", str(destination)))
        except Exception as exc:
            traceback.print_exc()
            try:
                self._copy_ready_audio(destination)
            except OSError:
                self.events.put(("error", friendly_error(exc)))
                return
            self.events.put(("downloaded_plain", str(destination)))

    def _reveal_download(self, destination: Path, message: str | None = None) -> None:
        self.set_status(message or ("បានទាញយក៖ " + str(destination)))
        subprocess.Popen(["explorer", f"/select,{destination}"])

    def finish_video_ui(self) -> None:
        try:
            self.progress.stop()
        except tk.TclError:
            pass
        self.progress.configure(mode="determinate", value=0, maximum=1)
        self.set_busy(False)

    def create_video(self) -> None:
        if self.busy:
            return
        story = self.story_text()
        if not story:
            self.set_status("សូមបិទភ្ជាប់អត្ថបទរឿងសិន។")
            return
        if not self.audio_is_ready() or self.ready_key != self.settings_key(story):
            self.set_status("សូមបង្កើតសំឡេងឱ្យរួចសិន ទើបបង្កើតវីដេអូពីរឿងនោះ។")
            return
        downloads = Path.home() / "Downloads"
        try:
            downloads.mkdir(parents=True, exist_ok=True)
            destination = downloads / f"{self.download_stem()}.mp4"
            number = 2
            while destination.exists():
                destination = downloads / f"{self.download_stem()} ({number}).mp4"
                number += 1
        except OSError as exc:
            messagebox.showerror("NITEAN", friendly_error(exc))
            return
        self.cancel.clear()
        self.was_playing = False
        self.player.stop()
        self.player.stop_bed()
        self.set_busy(True)
        self.progress.configure(mode="indeterminate", maximum=100)
        self.progress.start(12)
        self.set_status("កំពុងបង្កើតរូបភាពតាមអត្ថន័យរឿង...")
        threading.Thread(
            target=self._video_worker,
            args=(
                story,
                destination,
                self.music_on.get() and self.music_volume.get() > 0,
                self.music_volume.get() / 100,
            ),
            daemon=True,
        ).start()

    def _video_worker(self, story: str, destination: Path, with_music: bool, level: float) -> None:
        try:
            source = self.ready_path
            if source is None or not source.exists():
                raise OSError("រកឯកសារសំឡេងមិនឃើញ")
            if self.cancel.is_set():
                raise GenerationCancelled
            self.events.put(("status", "កំពុងបកអត្ថន័យរឿងជារូបភាព..."))
            duration = media_duration(source)
            scenes = story_scenes(story, duration)
            if not scenes:
                raise RuntimeError("រឿងមិនមានអត្ថបទសម្រាប់វីដេអូ")
            frames_dir = WORK_DIR / "frames"
            if frames_dir.exists():
                shutil.rmtree(frames_dir, ignore_errors=True)
            frames = render_story_images(
                scenes,
                frames_dir,
                self.cancel,
                lambda message: self.events.put(("status", message)),
            )
            if self.cancel.is_set():
                raise GenerationCancelled
            durations = [max(0.3, float(scene["end"]) - float(scene["start"])) for scene in scenes]
            self.events.put(("status", "កំពុងផ្គុំសំឡេងចូលវីដេអូ..."))
            audio = source
            if with_music:
                mixed = WORK_DIR / "video-audio.mp3"
                mix_horror_bed(source, ensure_horror_bed(), mixed, level)
                audio = mixed
            if self.cancel.is_set():
                raise GenerationCancelled
            self.events.put(("status", "កំពុងសរសេរឯកសារវីដេអូ..."))
            proc = build_story_video(frames, durations, audio, destination)
            self.export_proc = proc
            _stdout, error = proc.communicate()
            self.export_proc = None
            if self.cancel.is_set():
                raise GenerationCancelled
            if proc.returncode != 0 or not destination.exists() or destination.stat().st_size < 1000:
                detail = (error or b"").decode("utf-8", "ignore").strip()
                raise RuntimeError(detail[:240] or "បង្កើតវីដេអូមិនបាន")
            self.events.put(("video_done", {"path": str(destination)}))
        except GenerationCancelled:
            self.events.put(("video_done", {"cancelled": True}))
        except Exception as exc:
            traceback.print_exc()
            self.events.put(("video_done", {"error": friendly_error(exc)}))

    def _copy_ready_audio(self, destination: Path) -> None:
        sources = [self.ready_path, WORK_DIR / "voice.mp3"]
        last_error: OSError | None = None
        for source in sources:
            if source is None or not source.exists():
                continue
            try:
                shutil.copyfile(source, destination)
                return
            except OSError as exc:
                last_error = exc
        if last_error:
            raise last_error
        raise OSError("រកឯកសារសំឡេងមិនឃើញ")

    def _start_job(self, text: str, play_after: bool, preview: bool, save_to: str | None) -> None:
        if self.busy:
            return
        text = text.strip()
        if not text:
            self.set_status("សូមបិទភ្ជាប់អត្ថបទសិន។")
            return
        if not preview:
            self.user_cleared = False
            self.story_backup = text
            self.write_story(text)
        key = "" if preview else self.settings_key(text)
        if (
            play_after
            and not preview
            and save_to is None
            and key
            and key == self.ready_key
            and self.ready_path
            and self.ready_path.exists()
        ):
            self.start_playback(self.ready_path)
            self.set_status("ប្រើសំឡេងដែលបានបង្កើតរួច។")
            return

        self.player.close()
        self.player.stop_bed()
        self.was_playing = False
        self.pause_btn.configure(text="ផ្អាក")
        self.time_label.configure(text="00:00 / 00:00")
        self.cancel.clear()
        self.set_busy(True)
        self.phase = "gen"
        self.progress.configure(maximum=1, value=0)
        self.set_status("កំពុងរៀបចំអត្ថបទ...")
        threading.Thread(
            target=self._worker,
            args=(text, self.voice.get(), f"{self.speed.get():+d}%", self.pitch.get(), play_after, preview, save_to, key),
            daemon=True,
        ).start()

    def _worker(
        self,
        text: str,
        voice: str,
        rate: str,
        pitch: str,
        play_after: bool,
        preview: bool,
        save_to: str | None,
        key: str,
    ) -> None:
        try:
            asyncio.run(self._generate(text, voice, rate, pitch, play_after, preview, save_to, key))
        except GenerationCancelled:
            self.events.put(("status", "បានបញ្ឈប់ការបង្កើតសំឡេង។"))
            self.events.put(("idle", None))
        except Exception as exc:
            traceback.print_exc()
            self.events.put(("error", friendly_error(exc)))

    async def _generate(
        self,
        text: str,
        voice: str,
        rate: str,
        pitch: str,
        play_after: bool,
        preview: bool,
        save_to: str | None,
        key: str,
    ) -> None:
        chunks = split_text(text)
        if not chunks:
            raise RuntimeError("អត្ថបទទទេ")
        WORK_DIR.mkdir(parents=True, exist_ok=True)
        part_dir = WORK_DIR / ("preview-parts" if preview else "parts")
        if part_dir.exists():
            shutil.rmtree(part_dir, ignore_errors=True)
        part_dir.mkdir(parents=True, exist_ok=True)
        self.events.put(("max", len(chunks)))

        parts: list[Path] = []
        for index, chunk in enumerate(chunks, start=1):
            if self.cancel.is_set():
                raise GenerationCancelled
            self.events.put(("status", f"កំពុងបង្កើតសំឡេង  ផ្នែក {index}/{len(chunks)}"))
            self.events.put(("value", index - 1))
            part = part_dir / f"part_{index:03d}.mp3"
            await self._synth(chunk, part, voice, rate, pitch)
            parts.append(part)
            self.events.put(("value", index))
            await asyncio.sleep(0.15)

        if self.cancel.is_set():
            raise GenerationCancelled
        self.events.put(("status", "កំពុងផ្គុំសំឡេង..."))
        destination = WORK_DIR / ("preview.mp3" if preview else "voice.mp3")
        concat_mp3(parts, destination)
        merged_cues: list[dict] = []
        cue_offset = 0.0
        for part in parts:
            merged_cues.extend(shift_cues(read_cues(part), cue_offset))
            cue_offset += media_duration(part)
        write_cues(destination, merged_cues)
        final_path = destination
        if not preview:
            STATE_DIR.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(destination, CACHE_MP3)
            CACHE_KEY.write_text(key, encoding="utf-8")
            CUES_PATH.write_text(json.dumps(merged_cues, ensure_ascii=False), encoding="utf-8")
            final_path = CACHE_MP3
        if save_to:
            shutil.copyfile(final_path, save_to)
        self.events.put(
            (
                "done",
                {
                    "path": str(final_path),
                    "play": play_after,
                    "preview": preview,
                    "save_to": save_to,
                    "key": key,
                },
            )
        )

    async def _synth(self, text: str, dest: Path, voice: str, rate: str, pitch: str, depth: int = 0) -> None:
        text = text.strip()
        if not text:
            return
        try:
            await self._synth_once(text, dest, voice, rate, pitch)
        except GenerationCancelled:
            raise
        except Exception:
            if self.cancel.is_set():
                raise GenerationCancelled
            if depth >= 4 or len(text) < 40:
                raise
            left, right = split_half(text)
            if not left or not right:
                raise
            left_path = dest.with_name(f"{dest.stem}_L{depth}.mp3")
            right_path = dest.with_name(f"{dest.stem}_R{depth}.mp3")
            await self._synth(left, left_path, voice, rate, pitch, depth + 1)
            await self._synth(right, right_path, voice, rate, pitch, depth + 1)
            concat_mp3([left_path, right_path], dest)
            write_cues(
                dest,
                read_cues(left_path) + shift_cues(read_cues(right_path), media_duration(left_path)),
            )

    async def _synth_once(self, text: str, dest: Path, voice: str, rate: str, pitch: str) -> None:
        last: Exception | None = None
        for attempt in range(3):
            if self.cancel.is_set():
                raise GenerationCancelled
            try:
                communicate = edge_tts.Communicate(text, voice, rate=rate, pitch=pitch)
                audio = bytearray()
                cues: list[dict] = []
                async for message in communicate.stream():
                    if self.cancel.is_set():
                        raise GenerationCancelled
                    kind = message["type"]
                    if kind == "audio":
                        audio.extend(message["data"])
                    elif kind == "SentenceBoundary":
                        start = float(message["offset"]) / 10_000_000
                        end = start + float(message["duration"]) / 10_000_000
                        spoken = str(message.get("text") or "").strip()
                        if spoken and end > start:
                            cues.append(
                                {
                                    "start": round(start, 3),
                                    "end": round(end, 3),
                                    "text": spoken,
                                }
                            )
                if len(audio) < 128:
                    raise RuntimeError("សំឡេងទទេ")
                dest.write_bytes(audio)
                write_cues(dest, cues)
                return
            except GenerationCancelled:
                raise
            except Exception as exc:
                last = exc
                await asyncio.sleep(0.8 * (attempt + 1))
        if last:
            raise last
        raise RuntimeError("បង្កើតសំឡេងមិនបាន")

    def tick(self) -> None:
        if not self.alive:
            return
        try:
            self._drain_events()
            self._poll_player()
            self.root.after(200, self.tick)
        except tk.TclError:
            self.alive = False

    def _drain_events(self) -> None:
        try:
            while True:
                kind, payload = self.events.get_nowait()
                if kind == "status":
                    self.set_status(str(payload))
                elif kind == "max":
                    self.phase = "gen"
                    self.progress.configure(maximum=max(1, int(payload)), value=0)
                elif kind == "value":
                    if self.phase == "gen":
                        self.progress.configure(value=int(payload))
                elif kind == "error":
                    self.set_busy(False)
                    self.phase = "idle"
                    self.set_status(str(payload))
                    messagebox.showerror("NITEAN", str(payload))
                elif kind == "idle":
                    self.set_busy(False)
                    self.phase = "idle"
                elif kind == "video_done":
                    self.finish_video_ui()
                    info = dict(payload or {})
                    if info.get("cancelled"):
                        self.set_status("បានបញ្ឈប់ការបង្កើតវីដេអូ។")
                    elif info.get("error"):
                        self.set_status(str(info["error"]))
                        messagebox.showerror("NITEAN", str(info["error"]))
                    else:
                        path = Path(str(info["path"]))
                        self._reveal_download(path, "បានបង្កើតវីដេអូ៖ " + str(path))
                elif kind == "downloaded":
                    self.refresh_download()
                    self._reveal_download(Path(str(payload)))
                elif kind == "downloaded_plain":
                    self.refresh_download()
                    self.set_status("បានទាញយកសំឡេងសុទ្ធ ព្រោះលាយភ្លេងមិនបាន៖ " + str(payload))
                    subprocess.Popen(["explorer", f"/select,{payload}"])
                elif kind == "done":
                    self._on_done(payload)
        except queue.Empty:
            return

    def _on_done(self, payload: object) -> None:
        info = dict(payload)  # type: ignore[arg-type]
        self.set_busy(False)
        path = Path(str(info["path"]))
        if not info["preview"]:
            self.ready_path = path
            self.ready_key = str(info["key"])
        self.refresh_download()
        if info["save_to"]:
            self.set_status("បានរក្សាទុក៖ " + str(info["save_to"]))
        if info["play"]:
            self.start_playback(path)
            if not info["preview"] and self.player.opened:
                self.set_status(f"សំឡេងរួចរាល់។ កំពុងអានដោយ {self.voice_label()}។  ចុច «ទាញយក MP3» បានហើយ។")
            return
        self.phase = "idle"
        if not info["save_to"]:
            self.set_status("សំឡេងរួចរាល់។ ចុច «ទាញយក MP3» ដើម្បីទាញយក ឬ «ចាក់» ដើម្បីស្ដាប់។")

    def _poll_player(self) -> None:
        if self.phase != "play" or not self.player.opened:
            return
        mode = self.player.mode()
        position = self.player.position()
        length = max(1, self.player.length())
        self.time_label.configure(text=f"{format_ms(position)} / {format_ms(length)}")
        self.progress.configure(maximum=length, value=min(position, length))
        if mode == "playing":
            self.was_playing = True
            if self.music_on.get() and self.music_volume.get() > 0 and self.player.bed_mode() == "stopped":
                self.start_bed()
        elif mode == "stopped" and self.was_playing and not self.busy:
            self.was_playing = False
            self.phase = "idle"
            self.player.stop_bed()
            self.pause_btn.configure(text="ផ្អាក")
            if self.audio_is_ready():
                self.set_status("អានចប់ហើយ។ ចុច «ទាញយក MP3» ដើម្បីរក្សាទុកឯកសារ។")
            else:
                self.set_status("អានចប់ហើយ។")

    def schedule_persist(self) -> None:
        if self.persist_job is not None:
            self.root.after_cancel(self.persist_job)
        self.persist_job = self.root.after(800, self.persist_text)

    def write_story(self, story: str) -> None:
        story = story.strip()
        if not story or story == PLACEHOLDER:
            return
        STATE_DIR.mkdir(parents=True, exist_ok=True)
        temporary = TEXT_PATH.with_suffix(".writing.txt")
        temporary.write_text(story, encoding="utf-8")
        temporary.replace(TEXT_PATH)

    def story_to_save(self) -> str:
        content = ""
        try:
            content = self.text.get("1.0", "end-1c").strip()
        except tk.TclError:
            content = ""
        if content == PLACEHOLDER:
            content = ""
        if content:
            self.user_cleared = False
            self.story_backup = content
            return content
        if self.story_backup and not self.user_cleared:
            return self.story_backup
        return ""

    def persist_text(self) -> None:
        self.persist_job = None
        try:
            story = self.story_to_save()
            if story:
                self.write_story(story)
            elif self.user_cleared and not self.closing and TEXT_PATH.exists():
                TEXT_PATH.unlink()
        except OSError:
            return

    def persist_settings(self) -> None:
        try:
            STATE_DIR.mkdir(parents=True, exist_ok=True)
            SETTINGS_PATH.write_text(
                json.dumps(
                    {
                        "voice": self.voice.get(),
                        "rate": int(self.speed.get()),
                        "pitch": self.pitch.get(),
                        "music": bool(self.music_on.get()),
                        "music_volume": int(self.music_volume.get()),
                    }
                ),
                encoding="utf-8",
            )
        except OSError:
            return

    def _load_settings(self) -> None:
        if not SETTINGS_PATH.exists():
            return
        try:
            data = json.loads(SETTINGS_PATH.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            return
        voice = str(data.get("voice", ""))
        pitch = str(data.get("pitch", ""))
        if any(voice == value for value, _label in VOICES):
            self.voice.set(voice)
        if any(pitch == value for value, _label in PITCHES):
            self.pitch.set(pitch)
        try:
            rate = int(data.get("rate", -5))
        except (TypeError, ValueError):
            rate = -5
        self.speed.set(max(-30, min(30, rate)))
        if "music" in data:
            self.music_on.set(bool(data.get("music")))
        try:
            music_volume = int(data.get("music_volume", 24))
        except (TypeError, ValueError):
            music_volume = 24
        self.music_volume.set(max(0, min(100, music_volume)))

    def _load_story(self) -> None:
        if not TEXT_PATH.exists():
            return
        try:
            story = TEXT_PATH.read_text(encoding="utf-8").strip()
        except OSError:
            return
        if not story:
            return
        self.placeholder = False
        self.user_cleared = False
        self.story_backup = story
        self.text.configure(fg=FG)
        self.text.delete("1.0", "end")
        self.text.insert("1.0", story)
        self.text.edit_modified(False)
        self.update_count()

    def _restore_audio_cache(self) -> None:
        story = self.story_text()
        if not story or not CACHE_KEY.exists() or not CACHE_MP3.exists():
            return
        try:
            key = CACHE_KEY.read_text(encoding="utf-8").strip()
        except OSError:
            return
        if key == self.settings_key(story):
            self.ready_path = CACHE_MP3
            self.ready_key = key
            self.set_status("សំឡេងដែលបានបង្កើតពីមុននៅមាន។ ចុច «ទាញយក MP3» ឬ «ចាក់»។")

    def on_close(self) -> None:
        self.closing = True
        self.alive = False
        self.cancel.set()
        if self.placeholder_job is not None:
            self.root.after_cancel(self.placeholder_job)
            self.placeholder_job = None
        if self.persist_job is not None:
            self.root.after_cancel(self.persist_job)
            self.persist_job = None
        self.persist_text()
        self.persist_settings()
        self.player.close()
        self.player.close_bed()
        self.root.destroy()


def enable_dpi() -> None:
    try:
        ctypes.windll.shcore.SetProcessDpiAwareness(1)
    except Exception:
        try:
            ctypes.windll.user32.SetProcessDPIAware()
        except Exception:
            return


def main() -> None:
    try:
        enable_dpi()
        root = tk.Tk()
        app = KhmerVoiceApp(root)

        def report(_exc_type, exc, _tb) -> None:
            if app.alive:
                messagebox.showerror("NITEAN", friendly_error(exc))

        root.report_callback_exception = report
        root.mainloop()
    except Exception:
        STATE_DIR.mkdir(parents=True, exist_ok=True)
        (STATE_DIR / "error.log").write_text(traceback.format_exc(), encoding="utf-8")
        raise


if __name__ == "__main__":
    main()
