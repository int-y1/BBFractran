@echo off
del a.exe >nul 2>&1
g++ -O2 -std=c++20 -Wl,--stack,536870912 "%1.cpp"
.\a.exe
