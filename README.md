
# FSTRIPS-SMT

## Installation

Install the latest planner release with

    pip install fstripssmt


### Software Requirements
The planner requires Python >= 3.6.

## Development and Testing
If developing Tarski, we recommend cloning from the Github repository and doing a dev installation
(the`-e` flag for `pip`) on a [virtual environment](https://docs.python.org/3/tutorial/venv.html):
    
    git clone https://github.com/aig-upf/fstripssmt
    cd fstripssmt
    pip install -e .

This will install the project in "editable mode", meaning that any modification to the files
is immediately reflected in the _installed_ library.


**Testing**. All tests live under the `tests` directory.
To run them, you just need to run `pytest` (`pip install pytest`) on the root directory.
You can also run the tests through `tox` (`pip install tox`), for which several testing environments
[have been defined](tox.ini), e.g. to test the framework under different Python versions or apply static
analysis to the code.


## License
This planner is licensed under the [GNU General Public License, version 3](LICENSE).
