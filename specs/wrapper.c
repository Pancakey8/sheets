#include <lean/lean.h>
#include <stddef.h>
#include <string.h>

extern lean_object *initialize_sheets__specs_Sheets(uint8_t builtin);
extern void lean_initialize_runtime_module(void);
extern lean_object *run_lean_intrin(lean_object *);

int init_spec(void) {
  lean_initialize_runtime_module();
  lean_object *res = initialize_sheets__specs_Sheets(1);
  lean_io_mark_end_initialization();

  if (!lean_io_result_is_error(res)) {
    lean_dec_ref(res);
    return -1;
  }

  lean_dec_ref(res);
  return 0;
}

void run_lean(char const *input, size_t length, char **output) {
  lean_object *arr = lean_alloc_sarray(1, length, length);
  uint8_t *bytes = lean_sarray_cptr(arr);
  memcpy(bytes, input, length);
  lean_object *s = run_lean_intrin(arr);
  *output = strdup(lean_string_cstr(s));
  lean_dec(s);
}
