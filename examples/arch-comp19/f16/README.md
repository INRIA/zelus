# F16 Model

This model is used in the ARCH competition of 2019.
It has been described by Peter Heidlauf, Alexander Collins,
Michael Bolender and Stanley Bak in "Verification Challenges in F-16
Ground Collision Avoidance and Other Automated Maneuvers"

The current folder implements the 3rd case described in the paper :
the outer-loop performs Ground-Collision Avoidance.

Adapted from the [python version](https://github.com/stanleybak/AeroBenchVVPython) by Ismail Bennani (ismail.lahkim.bennani@ens.fr)

## How to run

```
make run_controlledf16.byte
./run_controlledf16.byte
```

## Files

* `matrix.ml`: very small matrix handling library used by `utils.zls`
* `utils.zls`: some useful functions, in particular some LUTs functions
* `types.zls`: record types are used instead of lists to improve readability
* `subf16_model.zls`: aircraft plant
* `lowLevelController.zls` : inner-loop controller
* `gcasAutopilot.zls`: outer-loop controller
* `controlledf16.zls`: composition of `subf16_model.zls`, `lowLevelController.zls` and `gcasAutopilot.zls`
* `run_controlledf16.byte`: main program, run the controlled f16 with predefined initial conditions
