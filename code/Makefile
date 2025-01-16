# Source and destination directories for lean files
SRC_LEAN_DIR := Cse230wi25/full
DST_LEAN_DIR := Cse230wi25/cut

SRC_LEAN_FILES := $(wildcard $(SRC_LEAN_DIR)/*.lean)
DST_LEAN_FILES := $(patsubst $(SRC_LEAN_DIR)/%.lean,$(DST_LEAN_DIR)/%.lean,$(SRC_LEAN_FILES))

lean_files: $(DST_LEAN_FILES)
	@echo "Lean source generation complete"

# Create dst directory if it doesn't exist
$(DST_LEAN_DIR):
	mkdir -p $(DST_LEAN_DIR)

$(DST_LEAN_DIR)/%.lean: $(SRC_LEAN_DIR)/%.lean | $(DST_LEAN_DIR)
	./convert.hs $< > $@
