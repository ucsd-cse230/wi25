# Source and destination directories
SRC_DIR := code/Cse230wi25
DST_DIR := src/lectures

# Get all .lean files in src directory
SRC_FILES := $(wildcard $(SRC_DIR)/*.lean)
# Generate corresponding .md file names in dst directory
DST_FILES := $(patsubst $(SRC_DIR)/%.lean,$(DST_DIR)/%.md,$(SRC_FILES))

# Default target - create all .md files
all: $(DST_FILES)
	@echo "Markdown generation complete"

# Create dst directory if it doesn't exist
$(DST_DIR):
	mkdir -p $(DST_DIR)

# Pattern rule: for each .lean file, create corresponding .md file
$(DST_DIR)/%.md: $(SRC_DIR)/%.lean | $(DST_DIR)
	scripts/convert.hs $< > $@

# Clean target
.PHONY: clean
clean:
	rm -rf $(DST_DIR)
