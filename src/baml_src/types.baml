// Output types for math problem extraction

// A single math problem found on a page
class MathProblem {
  problem_number string @description("The problem number/identifier (e.g., '2.82', 'Well-known problem')")
  problem_text string @description("The complete text of the math problem, excluding any answer if present")
  answer string? @description("The answer to the problem if one is provided in the text. For example: 'No, it is undecidable (N. Ya. Medvedev, Algebra and Logic, 44, no. 5 (2005), 302–312).' Leave null if no answer is given.")
}

// Output for extracting all problems from a page
class PageProblems {
  problems MathProblem[] @description("List of 0 to N math problems found on this page. Empty list if no problems found.")
}

// GAP code generation types

class GAPCode {
  code string @description("The GAP code to execute. Should be a single expression or statement, ending with semicolon. Example: 'Size(Centre(SymmetricGroup(4)));'")
  explanation string @description("Brief explanation of what this code does and why it answers the query")
}

class GAPCodeFix {
  fixed_code string @description("The corrected GAP code that should fix the error")
  reasoning string @description("Explanation of what was wrong and how this fixes it")
}