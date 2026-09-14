{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flakelight.url = "github:nix-community/flakelight";
  };
  outputs =
    inputs:
    inputs.flakelight ./. {
      inherit inputs;
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];
      devShell.packages =
        pkgs: with pkgs; [
          dune_3
          ocaml
          ocamlPackages.ocaml-lsp
          ocamlPackages.menhir
          ocamlPackages.menhirLib
          ocamlPackages.findlib
          ocamlPackages.batteries
          ocamlPackages.alcotest
          ocamlPackages.graphics
          ocamlPackages.ppx_deriving
          ocamlPackages.lablgtk
          ocamlPackages.z3
        ];
    };
}
