@echo off
cd /d "%~dp0"
python -c "import edge_tts" 1>nul 2>nul
if errorlevel 1 python -m pip install -r requirements.txt
where pythonw >nul 2>nul
if %errorlevel%==0 (
  start "" pythonw khmer_voice.py
) else (
  python khmer_voice.py
)
