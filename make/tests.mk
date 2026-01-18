# Test targets

# Run all tests
.PHONY: test
test:
	@echo "Running tests..."
	@uv run pytest tests/ -v

# Run tests with coverage
.PHONY: test-coverage
test-coverage:
	@echo "Running tests with coverage..."
	@uv run pytest tests/ --cov=src --cov-report=term-missing

# Run specific test file
.PHONY: test-gap
test-gap:
	@echo "Running GAP interface tests..."
	@uv run pytest tests/test_gap.py -v

# Clean test artifacts
.PHONY: clean-test
clean-test:
	@echo "Cleaning test artifacts..."
	@rm -rf .pytest_cache
	@rm -rf htmlcov
	@rm -f .coverage
	@echo "Test artifacts cleaned"