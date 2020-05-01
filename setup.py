from setuptools import setup, find_packages
from codecs import open
from os import path
import importlib

here = path.abspath(path.dirname(__file__))

# Get the long description from the README file
with open(path.join(here, 'README.md'), encoding='utf-8') as f:
    long_description = f.read()


# Load the version information from within the distribution files
spec = importlib.util.spec_from_file_location('fstripssmt.version', path.join(here, 'src/fstripssmt/version.py'))
version = importlib.util.module_from_spec(spec)
spec.loader.exec_module(version)


def main():

    setup(
        name='fstripssmt',
        version=version.__version__,
        description='A FSTRIPS planner based on Satisfiability Modulo Theories.',
        long_description=long_description,
        long_description_content_type='text/markdown',

        url='https://github.com/aig-upf/fstripssmt',
        author='Guillem Francès and Miquel Ramírez',
        author_email='guillem.frances@upf.edu',

        keywords='planning logic Fcuntional STRIPS SMT',
        classifiers=[
            'Development Status :: 3 - Alpha',

            'Intended Audience :: Science/Research',
            'Intended Audience :: Developers',

            'Topic :: Scientific/Engineering :: Artificial Intelligence',

            'License :: OSI Approved :: GNU General Public License v3 (GPLv3)',

            'Programming Language :: Python :: 3',
            'Programming Language :: Python :: 3.6',
            'Programming Language :: Python :: 3.7',
            'Programming Language :: Python :: 3.8',
        ],

        packages=find_packages('src'),  # include all packages under src
        package_dir={'': 'src'},  # tell distutils packages are under src


        install_requires=[
            'tarski[arithmetic]',
            'pysmt'
        ],

        extras_require={
            'dev': ['pytest', 'tox', 'pytest-cov', 'mypy'],
            'test': ['pytest', 'tox', 'pytest-cov', 'mypy'],
        },

        # This will include non-code files specified in the manifest, see e.g.
        # http://python-packaging.readthedocs.io/en/latest/non-code-files.html
        include_package_data=True,
    )


if __name__ == '__main__':
    main()
