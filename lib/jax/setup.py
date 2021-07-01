from setuptools import setup

setup(
    name="zlax",
    version="2.2",
    packages=["zlax"],
    description="Librairies for the Python backend of Zelus using JAX.",
    author="Reyyan Tekin",
    url="https://github.com/INRIA/zelus",
    install_requires=["jax"]
)
