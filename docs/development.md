
# Development

## Requirements

The project should run on top of any Python 3.6 installation.

## Setting Up Environment

We recommend using a dedicated 
[virtual environment](https://docs.python.org/3/tutorial/venv.html).
Once inside the virtual environment, run the following: 

    # Install the Tarski parser & preprocessor *in development mode*
    git clone git@github.com:aig-upf/tarski.git
    cd tarski
    pip install -e .
    
    # Install the project-specific code:
    git clone git@github.com:aig-upf/fstripssmt.git
    cd fstripssmt
    pip install -e .

    # Some other development packages: 
    pip install pytest
    
Now you'll need some actual SMT solver. 
You can e.g. install the Z3 SMT solver:

    pysmt-install --z3
    
You can check for alternatives through:

    pysmt-install --check