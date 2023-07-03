{
  description = "Categorical diagrams";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        py = pkgs.python310.withPackages (ps: with ps; [
          attrs click-repl
        ]);
        zaha = pkgs.stdenv.mkDerivation {
          name = "zaha";
          version = "0.0.1";

          src = ./.;

          buildPhase = ''
            echo "#!${py}/bin/python" > shebang
            sed -i -e 's,@GRAPHVIZ@,${pkgs.graphviz},' zaha.py
          '';

          installPhase = ''
            mkdir -p $out/bin/
            cat shebang zaha.py > $out/bin/zaha
            chmod +x $out/bin/zaha
            
            mkdir -p $out/share/
            cp -r analysis biology category complexity jbobau physics reverse topology $out/share/
          '';
        };
      in {
        packages = {
          default = zaha;
        };
        devShells.default = pkgs.mkShell {
          name = "zaha-env";
          packages = [];
        };
      }
    );
}
