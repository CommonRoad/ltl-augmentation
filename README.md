## LTL Augmentation: Augment LTL Formulas with Outside Knowledge

### System Requirements

The software is written in Python 3.10 and Rust, and was tested on Ubuntu 22.04.

### Building & Testing

To build the Rust code simply run
```bash
cargo build
```
This will automatically download all required dependencies.

You can run the tests with
```bash
cargo test
```

### Python Bindings

The project provides Python bindings for the most important functionalities.
To install the Python package, you need to run
```bash
pip install -v .
```
The `-v` switch activates additional output during the build process.

For development purposes, it can make sense to install the Python bindings directly via `maturin`:
```bash
maturin develop
```
`maturin` can be installed via `pip`.
For further options, please see its [documentation](https://www.maturin.rs/).

You can run the `main.py` script to check whether the Python bindings were installed properly.

### Using Pre-Commit Hooks

This project uses [pre-commit](https://pre-commit.com/) to ensure that formatters and linters automatically run when committing files.
To use pre-commit, install it via pip:

```bash
pip install pre-commit
```
Alternatively, pre-commit is also included in the optional `dev` dependencies of this project.

Then, install the pre-commit hooks so that they automatically run before each commit:
```bash
pre-commit install
```

To run the pre-commit hooks manually, use
```bash
pre-commit run --all-files
```
