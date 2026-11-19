@echo off
title AETHERION V2 Native Build
echo.
echo  AETHERION V2 Native — Full HDR Port
echo  ===================================
echo.

where gcc >nul 2>&1
if %errorlevel%==0 (
  echo Found GCC. Compiling...
  gcc aetherion_win.c -o aetherion.exe -lopengl32 -lgdi32 -luser32 -mwindows -O2
  if exist aetherion.exe (
    echo.
    echo  SUCCESS: aetherion.exe created
    echo  Controls: 1-4 worlds, WASD+mouse, F filter, T tone map, Space director
    echo.
    start aetherion.exe
  ) else (
    echo Compile failed. Check errors above.
  )
  goto end
)

where cl >nul 2>&1
if %errorlevel%==0 (
  echo Found Visual Studio cl. Compiling...
  cl aetherion_win.c /Fe:aetherion.exe /O2 /link opengl32.lib gdi32.lib user32.lib
  if exist aetherion.exe (
    echo.
    echo  SUCCESS: aetherion.exe created
    start aetherion.exe
  )
  goto end
)

echo.
echo  No compiler found.
echo  Install MinGW-w64 and add it to PATH, or open a
echo  "Developer Command Prompt for VS" and run this bat again.
echo.
echo  MinGW-w64: https://www.mingw-w64.org/
echo.

:end
pause
