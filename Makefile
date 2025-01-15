# Source and destination directories
SRC_DIR := code/Cse230wi25
DST_DIR := src/lectures

# Source and destination directories for lean files
SRC_LEAN_DIR := code/Cse230wi25/full
DST_LEAN_DIR := code/Cse230wi25/cut

# Get all .lean files in src directory
SRC_FILES := $(wildcard $(SRC_DIR)/*.lean)
# Generate corresponding .md file names in dst directory
DST_FILES := $(patsubst $(SRC_DIR)/%.lean,$(DST_DIR)/%.md,$(SRC_FILES))

SRC_LEAN_FILES := $(wildcard $(SRC_LEAN_DIR)/*.lean)
# Generate corresponding .md file names in dst directory
DST_LEAN_FILES := $(patsubst $(SRC_LEAN_DIR)/%.lean,$(DST_LEAN_DIR)/%.lean,$(SRC_LEAN_FILES))

# Default target - create all .md files
all: $(DST_FILES)
	@echo "Markdown generation complete"

# Create dst directory if it doesn't exist
$(DST_DIR):
	mkdir -p $(DST_DIR)

# Pattern rule: for each .lean file, create corresponding .md file
$(DST_DIR)/%.md: $(SRC_DIR)/%.lean | $(DST_DIR)
	scripts/convert.hs $< > $@

upload: all
	git commit -a -m "update"
	git push origin main

# Clean target
.PHONY: clean
clean:
	rm -rf $(DST_DIR)

lean_files: $(DST_LEAN_FILES)
	@echo "Lean source generation complete"

# Create dst directory if it doesn't exist
$(DST_LEAN_DIR):
	mkdir -p $(DST_LEAN_DIR)

$(SRC_DIR)/%.lean: $(SRC_LEAN_DIR)/%.lean | $(DST_LEAN_DIR)
	scripts/convert_lean.hs $< > $@
