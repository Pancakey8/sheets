clang -o demo demo.c \
  -L.lake/build/lib \
  -L.lake/packages/mathlib/.lake/build/lib \
  -L.lake/packages/batteries/.lake/build/lib \
  -L.lake/packages/aesop/.lake/build/lib \
  -L.lake/packages/Qq/.lake/build/lib \
  -L.lake/packages/proofwidgets/.lake/build/lib \
  -L.lake/packages/importGraph/.lake/build/lib \
  -L.lake/packages/plausible/.lake/build/lib \
  -L.lake/packages/LeanSearchClient/.lake/build/lib \
  -Wl,--no-as-needed \
  -lsheets__specs_Sheets \
  -lmathlib_Mathlib \
  -lbatteries_Batteries \
  -laesop_Aesop \
  -lQq_Qq \
  -lproofwidgets_ProofWidgets \
  -limportGraph_ImportGraph \
  -lplausible_Plausible \
  -lLeanSearchClient_LeanSearchClient \
  $(leanc --print-ldflags)

# Runs with:
# LD_LIBRARY_PATH="$(lean --print-prefix)/lib/lean:$PWD/.lake/build/lib:$PWD/.lake/packages/mathlib/.lake/build/lib:$PWD/.lake/packages/batteries/.lake/build/lib:$PWD/.lake/packages/aesop/.lake/build/lib:$PWD/.lake/packages/Qq/.lake/build/lib:$PWD/.lake/packages/proofwidgets/.lake/build/lib:$PWD/.lake/packages/importGraph/.lake/build/lib:$PWD/.lake/packages/plausible/.lake/build/lib:$PWD/.lake/packages/LeanSearchClient/.lake/build/lib" ./demo
