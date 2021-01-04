# Zelus Examples

Build all examples with
```
make
```

The executables can be found in each example directory (e.g., `horloge/horloge_main.exe`).

To build only one example pass the path to the executable to make:
```
make horloge/horloge_main.exe
```

The name of the executable is usually the name of the main zelus file (e.g., `horloge`) followed by the name of the simulation node (the `-s` option of the compiler, e.g., `main` ).
