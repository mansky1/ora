# Forward most targets to Rocq makefile (with some trick to make this phony)
%: Makefile.rocq phony
	+@make -f Makefile.rocq $@

all: Makefile.rocq
	+@make -f Makefile.rocq all
.PHONY: all

clean: Makefile.rocq
	+@make -f Makefile.rocq clean
	find theories tests exercises solutions \( -name "*.d" -o -name "*.vo" -o -name "*.vo[sk]" -o -name "*.aux" -o -name "*.cache" -o -name "*.glob" -o -name "*.vio" \) -print -delete || true
	rm -f Makefile.rocq .lia.cache
.PHONY: clean

# Create Coq Makefile.
Makefile.rocq: _RocqProject Makefile
	"$(COQBIN)rocq" makefile -f _RocqProject -o Makefile.rocq

# Install build-dependencies
build-dep/opam: opam Makefile
	@echo "# Creating build-dep package."
	@mkdir -p build-dep
	@sed <opam -E 's/^(build|install|remove):.*/\1: []/; s/^name: *"(.*)" */name: "\1-builddep"/' >build-dep/opam
	@fgrep builddep build-dep/opam >/dev/null || (echo "sed failed to fix the package name" && exit 1) # sanity check

build-dep: build-dep/opam phony
	@# We want opam to not just instal the build-deps now, but to also keep satisfying these
	@# constraints.  Otherwise, `opam upgrade` may well update some packages to versions
	@# that are incompatible with our build requirements.
	@# To achieve this, we create a fake opam package that has our build-dependencies as
	@# dependencies, but does not actually install anything itself.
	@echo "# Installing build-dep package."
	@opam install $(OPAMFLAGS) build-dep/

# Some files that do *not* need to be forwarded to Makefile.coq
Makefile: ;
_RocqProject: ;
opam: ;

# Phony wildcard targets
phony: ;
.PHONY: phony
