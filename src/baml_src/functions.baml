// Function to extract math problems from a PDF page

function ExtractProblems(page_text: string, page_number: int) -> PageProblems {
  client GPT4o
  prompt #"
    You are an expert at extracting mathematical problems from academic texts.
    
    {{ _.role("user") }}
    Extract all math problems from this page of a mathematical problem collection.
    
    Page number: {{ page_number }}
    
    IMPORTANT RULES:
    1. Look for numbered problems (e.g., "Problem 2.82", "2.82.", etc.)
    2. Also look for special problems like "(Well-known problem)"
    3. Extract the COMPLETE problem text, including all details, questions, and references
    4. For problem_number, use the exact identifier (e.g., "2.82", "Well-known problem")
    5. If a page has NO problems (e.g., title page, contents, preface), return an empty list
    6. Include editors' comments and citations that are part of the problem
    7. Problems often span multiple lines - capture everything until the next problem starts
    
    EXAMPLES OF VALID PROBLEMS:
    - problem_number: "Well-known problem"
      problem_text: "Can the group ring Z[G] of a torsion-free group G contain zero divisors?"
      answer: null
    
    - problem_number: "2.82"
      problem_text: "Can the class of groups with the nth Engel condition [x, y, . . . , y | {z } n ] = 1 be defined by identical relations of the form u = v, where u and v are words without negative powers of variables? This can be done for n = 1, 2, 3 (A. I. Shirshov, Algebra i Logika, 2, no. 5 (1963), 5–18 (Russian)). Editors' comment: This has also been done for n = 4 (G. Traustason, J. Group Theory, 2, no. 1 (1999), 39–46). As remarked by O. Macedo´nska, this is also true for the class of locally graded n-Engel groups because by (Y. Kim, A. Rhemtulla, in Groups–Korea'94, de Gruyter, Berlin, 1995, 189–197) such a group is locally nilpotent and then by (R. G. Burns, Yu. Medvedev, J. Austral. Math. Soc., 64 (1998), 92–100) such a group is an extension of a nilpotent group of n-bounded class by a group of nbounded exponent; then a classical result of Mal'cev implies that such groups satisfy a positive law."
      answer: null
    
    - problem_number: "5.20"
      problem_text: "Is the elementary theory of lattices of l-ideals of lattice-ordered abelian groups decidable? A. I. Kokorin"
      answer: "No, it is undecidable (N. Ya. Medvedev, Algebra and Logic, 44, no. 5 (2005), 302–312)."
    
    Page text:
    {{ page_text }}
    
    {{ ctx.output_format }}
  "#
}