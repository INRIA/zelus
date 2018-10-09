# Automatic Transmission Controller
#### [sldemo_autotrans](https://fr.mathworks.com/help/simulink/examples/modeling-an-automatic-transmission-controller.html)

Files:
- `consts.ml`: lookup tables constants
- `utils.ml`: lookup tables functions
- `draw.ml`: GUI to interact with the simulation
- `common.zls`: common code for the continuous and the discrete versions
- `autotransc.zls`: main functions for the continuous version
- `autotrans_gui.zls`: continuous version using a GUI to get inputs (see draw.ml)
- `autotransd.zls`: discrete version with a predefined input
