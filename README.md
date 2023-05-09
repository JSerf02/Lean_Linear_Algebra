# Lean_Linear_Algebra
## Setup
1. Open the parent folder of where you want this repository in VSCode.
2. Open the VSCode terminal.
3. Run `git clone https://github.com/JSerf02/Lean_Linear_Algebra.git Linear_Algebra`. It is important that you don't change the name of the destination folder from "Linear_Algebra" since Lean will specificalaly check for the folder's name when building and all of the files in this repo are configured with the folder name "Linear_Algebra" in mind.
4. Open the newly-created "Linear_Algebra" folder in VSCode. You should see all of the files, though they shouldn't work yet.
5. Open the VSCode terminal.
6. Run `lake update`. This will download and install `mathlib4` and its dependencies.
7. Run `cp lake-packages/mathlib/lean-toolchain .`. Notice the dot at the end of this command! This will make sure `mathlib4` is compatible with the version of Lean that you are using.
8. Run `lake exe cache get`. This will download the cache for `mathlib4`, which decrease the loading time from 30+ minutes to just a couple of seconds. If this doesn't work, you will have to find a way to install `curl 7.64` or later.
9. Run `lake build`. If you get no errors, everything worked!


You can test if this worked by opening the folder "LinearAlgebra/VectorSpace.lean" and highlighting the `VectorSpace` structure. If you get a summary of the structure, everything worked!

## Usage
To create a new module, create a file "<new_module>.lean" in the "LinearAlgebra" folder and then add `import <new_module>` to "LinearAlgebra.lean"

Try to keep unrelated topics as separate as possible, as we don't want this project to devolve into a single, giant code file!
