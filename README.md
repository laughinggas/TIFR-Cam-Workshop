This is the repository for the workshop on Lean 4 taking place at TIFR-Cam in September 2023. 

## Workshop plan
In this workshop, we shall go through some exercises to learn how to formalize various pieces of mathematics in Lean 4. Depending on the ability and interest of the user, we have 3 projects available :
1. Easy - Formalization of properties of natural numbers. This is for the first time user, and will help build a foundation.
2. Intermediate - We shall look at new definitions relating to Dirichlet characters. The task is to formalize properties arising from the definitions. If possible, we will try to get to the definition of generalized Bernoulli numbers.
3. Advanced - This is for experienced Lean users, who would also like a mathematical challenge. The challenge is to formalize a paper solving the Pizza Conjecture. It involves making definitions and proving properties pertaining to these definitions.

## Installation instructions
It is highly recommended that users install Mathlib 4 on their laptops before attending the workshop. Installation instructions are given [here](https://leanprover-community.github.io/install/windows.html). Once installed, please follow these instructions in order to get a local copy of this repository :
1. If you have not logged in since you installed Lean and mathlib, then you may need to first type `source ~/.profile` or `source ~/.bash_profile` depending on your OS.
2. Go the the directory where you would like this repository to live.
3. Run `git clone https://github.com/laughinggas/TIFR-Cam-Workshop`
4. Run `cd TIFR-Cam-Workshop`
5. Run `lake exe cache get`
6. Launch VS Code, either through your application menu or by typing `code .`
7. If you launched VS Code from a menu, on the main screen, or in the File menu, click "Open folder" (just "Open" on a Mac), and choose the folder `TIFR-Cam-Workshop` (not one of its subfolders).
8. Open the file `Try.lean` (or any of the files in the folder Exercises. If the orange bars disappear after a while, it means you are ready.

Happy Leaning!
