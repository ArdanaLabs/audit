{ pkgs ? import <nixpkgs> {} }:
# python.on-nix doesn't support jupyter yet, so this .nix file is defunct. 
let
  pythonOnNix = import
    (builtins.fetchGit {
      # Use `main` branch or a commit from this list:
      # https://github.com/on-nix/python/commits/main
      ref = "main";
      url = "https://github.com/on-nix/python";
    }) { inherit pkgs; };
  env = pythonOnNix.python39Env {
    name = "Danaswap-analytics";
    projects = {
      pandas = "latest";
      numpy = "latest";
      altair = "latest";
      seaborn = "latest";
      matplotlib = "latest";
      arviz = "latest";
      jupyterlab = "latest";
      jupyterlab-widgets = "latest";
      # nbformat = "latest";
      # ipykernel = "latest";
      # ipython = "latest";
      jax = "latest";
      numpyro = "latest";
    };
  };
in env.dev
