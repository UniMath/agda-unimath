# Scripts/hooks

We have included Python scripts/hooks for continuous integration which should
run on almost any platform. To run these, first install pre-commit and the other
Python requirements by running the following command in the terminal:

```shell
pip install -r requirements.txt
```

Now, before you commit next time, run `pre-commit` by executing

```shell
make pre-commit
```

in the terminal. This will run all the hooks.
