{
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  ## The attribute to build from the local sources,
  ## either using nixpkgs data or the overlays located in `.nix/coq-overlays`
  ## Will determine the default main-job of the bundles defined below
  attribute = "mathcomp-abel";

  ## If you want to select a different attribute (to build from the local sources as well)
  ## when calling `nix-shell` and `nix-build` without the `--argstr job` argument
  # shell-attribute = "{{nix_name}}";

  ## Maybe the shortname of the library is different from
  ## the name of the nixpkgs attribute, if so, set it here:
  # pname = "{{shortname}}";

  ## Lists the dependencies, phrased in terms of nix attributes.
  ## No need to list Coq, it is already included.
  ## These dependencies will systematically be added to the currently
  ## known dependencies, if any more than Coq.
  ## /!\ Remove this field as soon as the package is available on nixpkgs.
  ## /!\ Manual overlays in `.nix/coq-overlays` should be preferred then.
  # buildInputs = [ ];

  ## Indicate the relative location of your _CoqProject
  ## If not specified, it defaults to "_CoqProject"
  # coqproject = "_CoqProject";

  ## select an entry to build in the following `bundles` set
  ## defaults to "default"
  default-bundle = "coq8.20+mcmathcomp-2.3.0";

  ## write one `bundles.name` attribute set per
  ## alternative configuration
  ## When generating GitHub Action CI, one workflow file
  ## will be created per bundle
  bundles = let
    gen = coqv: mcv: elpiv:
      { "coq${coqv}+mc${mcv}" = {
        coqPackages = {
          coq.override.version = coqv;
          mathcomp.override.version = mcv;
          mathcomp.job = false;
        } // (if (coqv == "master") then {
          coq-elpi.override.version = "master";
          hierarchy-builder.override.version = "master";
        } else {}) // {
          mathcomp-real-closed.override.version = "master";
          mathcomp-bigenough.override.version = "1.0.1";
        };
        ocamlPackages = if (elpiv != "") then { elpi.override.version = elpiv; } else {};
      }; }; in
    gen "8.18" "mathcomp-2.1.0" "" //
    gen "8.19" "mathcomp-2.2.0" "" //
    gen "8.20" "mathcomp-2.3.0" "" // {
      "coq-9.0".coqPackages = {
        coq.override.version = "9.0";
        coq-elpi.job = true;
        hierarchy-builder.job = true;
        mathcomp-real-closed.override.version = "master";
        mathcomp-bigenough.override.version = "1.0.2";
      };
      "coq-master" = { rocqPackages = {
        rocq-core.override.version = "master";
        rocq-elpi.override.version = "master";
        rocq-elpi.override.elpi-version = "2.0.7";
        stdlib.override.version = "master";
        bignums.override.version = "master";
      }; coqPackages = {
        coq.override.version = "master";
        coq-elpi.override.version = "master";
        coq-elpi.override.elpi-version = "2.0.7";
        hierarchy-builder.override.version = "master";
        mathcomp.override.version = "master";
        mathcomp-real-closed.override.version = "master";
        mathcomp-bigenough.override.version = "1.0.2";
        stdlib.override.version = "master";
        bignums.override.version = "master";
      }; };
    };

  ## Cachix caches to use in CI
  ## Below we list some standard ones
  cachix.coq = {};
  cachix.math-comp.authToken = "CACHIX_AUTH_TOKEN";
  cachix.coq-community = {};
  
  ## If you have write access to one of these caches you can
  ## provide the auth token or signing key through a secret
  ## variable on GitHub. Then, you should give the variable
  ## name here. For instance, coq-community projects can use
  ## the following line instead of the one above:
  # cachix.coq-community.authToken = "CACHIX_AUTH_TOKEN";
  
  ## Or if you have a signing key for a given Cachix cache:
  # cachix.my-cache.signingKey = "CACHIX_SIGNING_KEY"
  
  ## Note that here, CACHIX_AUTH_TOKEN and CACHIX_SIGNING_KEY
  ## are the names of secret variables. They are set in
  ## GitHub's web interface.
}
