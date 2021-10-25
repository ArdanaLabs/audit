with import <nixpkgs> {};
let
  my-python-packages = python-packages: with python-packages; [
    jupyterlab
    ipywidgets
    pandas
    numpy
    altair
    seaborn
    matplotlib
  ]; 
  python-with-my-packages = python3.withPackages my-python-packages;
in python-with-my-packages.env
