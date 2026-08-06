CXX ?= clang++

CXXFLAGS += -std=c++23 -Wall -Wextra

SRCS := sheets.cpp main.cpp
OBJS := $(SRCS:%.cpp=%.o)

LEAN_LDFLAGS := $(shell cd specs && lake env leanc --print-ldflags)
LEAN_PREFIX := $(shell cd specs && lake env lean --print-prefix)

all: sheets sheets_test

%.o: %.cpp
	$(CXX) $(CXXFLAGS) -c -o $@ $^

sheets: $(OBJS)
	$(CXX) -o $@ $^

spec: specs/lakefile.lean specs/Sheets.lean specs/wrapper.c
	cd specs && lake build

sheets_test: sheets_test.o | spec
	$(eval LDIRS := $(shell find specs/.lake/ -type f -name 'lib*.so' -exec dirname {} \; | xargs printf '-L%s '))
	$(eval LIBS := $(shell find specs/.lake/ -type f -name 'lib*.so' | sed -E 's|.*/lib([^/]+)\.so|-l\1|'))
	clang -o $@ $^ \
		$(LDIRS) \
		-Wl,--no-as-needed \
		$(LIBS) \
		$(LEAN_LDFLAGS)

env:
	$(eval LPATH := $(shell find specs/.lake/ -type f -name 'lib*.so' -exec dirname {} \; | paste -sd:):$(LEAN_PREFIX)/lib/lean)
	@echo export LD_LIBRARY_PATH="$(LPATH)"

clean:
	rm -f $(OBJS) sheets_test.o
	cd specs && lake clean
