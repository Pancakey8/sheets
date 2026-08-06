#include <cstdio>
#include <cstdlib>

extern "C" int init_spec(void);
extern "C" void run_lean(char const *input, size_t length, char **output);

int main(void) {
  init_spec();

  char input[] = {
    1, // Set ⟨2, 1⟩ (atom (number 3.125))
    2, 0, 0, 0,
    1, 0, 0, 0,
    1, 0, 0, 0, 0, 0, 0, 9, 64,

    1, // Set ⟨2, 2⟩ (atom (number 8.0))
    2, 0, 0, 0,
    2, 0, 0, 0,
    1, 0, 0, 0, 0, 0, 0, 32, 64,

    1, // Set ⟨3, 1⟩ (add (ref ⟨2, 1⟩) (ref ⟨2, 2⟩))
    3, 0, 0, 0,
    1, 0, 0, 0,
    7, 4, 2, 0, 0, 0, 1, 0, 0, 0,
           4, 2, 0, 0, 0, 2, 0, 0, 0,

    3 // Evaluate
  };

  char *out;
  run_lean(input, sizeof(input), &out);
  std::puts(out);

  std::free(out);

  return 0;
}
