# tacas2020-exps
Experiments for TACAS 2020 submission

# Instructions
The easiest way to run the examples is to use the supplied `Dockerfile`.

Run `docker build -t tacas ./docker` to build the image.

Once this has completed, run `docker run -it --rm tacas` to run a container interactively.

## Running benchmarks
Start by entering this repository in the docker container: `cd tacas2020-exps`.

There are three benchmark categories:
* `shift_register`
* `circular_pointer`
* `arbitrated`

There are three main scripts to run the benchmarks:
* `check-en.py`: Checks the enable conditions
* `por-<benchmark>.py`: Checks the POR and RIS conditions
* `run.py`: Runs the example

For example, to compare the time to find the bug in the depth=16 width=16 shift register with and without POR/RIS, run the following:
```
./check-en.py shift_register --width 16 --depth 16
./por-shift_register.py --width 16 --depth 16
# run without POR/RIS
time ./run.py shift_register --width 16 --depth 16
# run with POR/RIS
time ./run.py shift_register --width 16 --depth 16 --por
```

# Artifact

The artifact_files directory includes a python virtual environment and copies of
all the necessary libraries for running the examples in the TACAS provided
virtual machine without any internet access.

# Logs
The log files from our experimental runs are provided in `opensource-results.tar.gz`.

# Notes
* Boolector commit hash was wrong in paper -- it seems like the branch may have been force pushed and lost that commit
