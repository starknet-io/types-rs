SRC_DIR ?= src/v0_7_1

define generate_spec
	echo "Generating types for $(1)";
	openrpc-gen --config $(1).toml --document $(1).json --output $(1).rs ;
endef

BASE_NAMES := starknet_api_openrpc starknet_trace_api_openrpc starknet_write_api
# Default target that depends on all generated .rs files
all: 
	$(foreach file,$(BASE_NAMES),$(call generate_spec,$(SRC_DIR)/$(file)))

# Phony target to avoid conflicts with actual files
.PHONY: all
