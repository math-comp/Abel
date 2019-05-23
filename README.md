# Developing Abel Theorem

## With nix.

1. Unless nix is already installed, install nix (you may still do this several
   times without suffering consequences).
   - To install it on a single-user unix system where you
     have `sudo` rights, just type:
     > sh <(curl https://nixos.org/nix/install)

   (for other configurations, refer to the [appropriate section of the
   nix manual](https://nixos.org/nix/manual/#ch-installing-binary)

   - In order to add `nix` environment variables right now, type:
     > . $HOME/.nix-profile/etc/profile.d/nix.sh

     the nix installer nix will automatically add this to your
     `.profile`, but **you need to log out and in again** for your shell
     to take this change into account. Also if you have an custom
     shell startup sequence, you should make sure this is executed at
     some point.

Once you logged out and in again you may start from 2. next time:

2. In order to open a shell with the right work environment, simply
   type in a **new terminal**:
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
