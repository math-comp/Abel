# Developing Abel Theorem

## With nix.

1. Install nix:
   - To install it on a single-user unix system where you
     have `sudo` rights, just type:
     > sh <(curl https://nixos.org/nix/install)

   For other configurations or for nix uninstallation,
   go to the [appropriate section of the
   nix manual](https://nixos.org/nix/manual/#ch-installing-binary).

   - Run the nix installer, which will set `nix` environment variables, by typing:
     > . $HOME/.nix-profile/etc/profile.d/nix.sh

     The nix installer will automatically update your
     `.profile`, but **you need to log out and in again** for your shell
     to take this change into account. If you have an custom
     shell startup sequence, make sure that this script is executed at
     some point.


Once you logged out and in again, go to step 2.

2. In order to open a shell with the right work environment, simply
   type in a **new terminal from the root of the repository**:
   > nix-shell
   - This will download and build the required packages, wait until
     you get a shell.
   - You need to type this command every time you open a new terminal.

3. You are now in the correct work environment. You can do
   > make
   
   and do whatever you are accustomed to do with Coq.

4. You can edit files using:
   > emacs
   - If you are using emacs with proof general, make sure you empty your
     `coq-prog-name` variables and any other proof general options that
     used to be tied to a previous local installation of Coq.
   - If you do not have emacs installed, you can go back to
     step 2. and call `nix-shell` with the following option
     > nix-shell --arg withEmacs true
     
     instead. Make sure you add `(require 'proof-site)` to your `.emacs`.
