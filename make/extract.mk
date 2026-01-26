# Extraction targets for multiple problem lists

.PHONY: extract-kourovka
extract-kourovka:
ifndef START
	@echo "Error: START and END variables are required"
	@echo "Usage: make extract-kourovka START=1 END=100"
	@exit 1
endif
ifndef END
	@echo "Error: START and END variables are required"
	@echo "Usage: make extract-kourovka START=1 END=100"
	@exit 1
endif
	@echo "Extracting Kourovka problems from pages $(START)-$(END)..."
	PYTHONPATH=src uv run python src/extraction/extract_clean.py \
		"lit/open-problems.pdf" \
		"problems/kourovka/extracted_$(START)_$(END).json" \
		$(START) $(END) --list kourovka

.PHONY: extract-klee
extract-klee:
ifndef START
	@echo "Error: START and END variables are required"
	@echo "Usage: make extract-klee START=1 END=10"
	@exit 1
endif
ifndef END
	@echo "Error: START and END variables are required"
	@echo "Usage: make extract-klee START=1 END=10"
	@exit 1
endif
	@echo "Extracting Klee geometry problems from pages $(START)-$(END)..."
	PYTHONPATH=src uv run python src/extraction/extract_clean.py \
		"lit/Unsolved_Problems_In_Intuitive_Geometry.pdf" \
		"problems/klee/extracted_$(START)_$(END).json" \
		$(START) $(END) --list klee

.PHONY: extract-all-kourovka
extract-all-kourovka:
	@echo "Extracting ALL Kourovka problems (full document)..."
	@echo "This will take several minutes and make many API calls."
	@read -p "Continue? (y/N): " confirm && [ "$$confirm" = "y" ] || exit 1
	PYTHONPATH=src uv run python src/extraction/extract_clean.py \
		"lit/open-problems.pdf" \
		"problems/kourovka/all_problems_raw.json" \
		--list kourovka

.PHONY: extract-all-klee
extract-all-klee:
	@echo "Extracting ALL Klee geometry problems (63 pages)..."
	@echo "This will take several minutes and make many API calls."
	@read -p "Continue? (y/N): " confirm && [ "$$confirm" = "y" ] || exit 1
	PYTHONPATH=src uv run python src/extraction/extract_clean.py \
		"lit/Unsolved_Problems_In_Intuitive_Geometry.pdf" \
		"problems/klee/all_problems.json" \
		--list klee