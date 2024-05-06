.PHONY: fuzz-add fuzz-div fuzz-mul fuzz-conversions

fuzz-add_sub:
	cargo +nightly fuzz run add_sub_fuzzer --fuzz-dir=./felt

fuzz-div:
	cargo +nightly fuzz run div_fuzzer --fuzz-dir=./felt

fuzz-mul:
	cargo +nightly fuzz run mul_fuzzer --fuzz-dir=./felt

fuzz-conversions:
	cargo +nightly fuzz run conversions_fuzzer --fuzz-dir=./felt
