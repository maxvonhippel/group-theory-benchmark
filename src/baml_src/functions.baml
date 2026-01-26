// GAP Code Generation Functions

function GenerateGAPCode(query: string) -> GAPCode {
  client GPT4o
  prompt #"
    You are an expert at writing GAP (Groups, Algorithms, Programming) code for computational group theory.

    {{ _.role("system") }}

    # GAP SYNTAX REFERENCE

    ## Core Constructs
    - Functions end with semicolon: `Size(G);`
    - Control flow: `if...then...elif...else...fi`, `for...in...do...od`, `while...do...od`
    - Function definition: `name := function(args) ... end;`
    - Comments: `# comment text`

    ## Common Group Constructors
    - `SymmetricGroup(n)` - Symmetric group Sₙ
    - `AlternatingGroup(n)` - Alternating group Aₙ
    - `CyclicGroup(n)` - Cyclic group Cₙ
    - `DihedralGroup(n)` - Dihedral group Dₙ
    - `SmallGroup(order, index)` - Group from library (e.g., `SmallGroup(8, 3)`)
    - `DirectProduct(G1, G2)` - Direct product

    ## Property Checks (return true/false)
    - `IsAbelian(G)` - Is group abelian?
    - `IsCyclic(G)` - Is group cyclic?
    - `IsSimple(G)` - Is group simple?
    - `IsSolvable(G)` - Is group solvable?
    - `IsNilpotent(G)` - Is group nilpotent?
    - `IsPerfect(G)` - Is group perfect?

    ## Group Invariants
    - `Size(G)` - Order of group
    - `Centre(G)` or `Center(G)` - Center of group (returns subgroup)
    - `DerivedSubgroup(G)` - Commutator subgroup
    - `ConjugacyClasses(G)` - List of conjugacy classes
    - `CharacterTable(G)` - Character table

    ## SmallGroups Library (requires LoadPackage("SmallGrp"))
    - `NrSmallGroups(n)` - Number of groups of order n
    - `SmallGroup(n, i)` - ith group of order n
    - `IdGroup(G)` - [order, index] identifying G in library
    - `AllSmallGroups(n)` - All groups of order n

    ## Lists and Filtering
    - `List([1..10], x -> x^2)` - Map function over list
    - `Filtered(list, predicate)` - Filter list
    - `[1..10]` - Range from 1 to 10
    - `First(list, predicate)` - Find first matching element

    ## Operator Precedence (highest to lowest)
    1. `^` (power)
    2. Unary `+`, `-`
    3. `*`, `/`, `mod`
    4. Binary `+`, `-`
    5. `=`, `<>`, `<`, `>`, `in`
    6. `not`
    7. `and`, `or`

    ## Examples

    Query: "Is S_4 abelian?"
    Code: `IsAbelian(SymmetricGroup(4));`

    Query: "What is the order of the center of A_5?"
    Code: `Size(Centre(AlternatingGroup(5)));`

    Query: "How many groups of order 12 are there?"
    Code: `LoadPackage("SmallGrp"); NrSmallGroups(12);`

    Query: "Find all non-abelian groups of order 8"
    Code: `LoadPackage("SmallGrp"); Filtered([1..NrSmallGroups(8)], i -> not IsAbelian(SmallGroup(8, i)));`

    Query: "Is the symmetric group S_3 isomorphic to the dihedral group D_3?"
    Code: `IsomorphismGroups(SymmetricGroup(3), DihedralGroup(6)) <> fail;`

    Query: "What are the orders of all conjugacy classes in A_4?"
    Code: `List(ConjugacyClasses(AlternatingGroup(4)), Size);`

    {{ _.role("user") }}

    Generate GAP code to answer this query:
    {{ query }}

    IMPORTANT:
    - Return ONLY valid GAP code that can be executed directly
    - Code must end with semicolon
    - If using SmallGroups library, include `LoadPackage("SmallGrp");` first
    - Keep it concise - one or two lines maximum
    - Make sure syntax is correct

    {{ ctx.output_format }}
  "#
}

// Function to extract geometry problems from Klee & Wagon

function ExtractKleeProblems(page_text: string, page_number: int) -> PageProblems {
  client GPT4o
  prompt #"
    Extract all geometry problems from this page of "Unsolved Problems in Intuitive Geometry" by Klee & Wagon.
    
    Page number: {{ page_number }}
    
    IMPORTANT RULES:
    1. Look for problems with K-prefix numbering (e.g., "K-1", "K-2", "K-23", etc.)
    2. Problems may span multiple paragraphs with mathematical notation
    3. Extract the COMPLETE problem statement including all parts (a), (b), etc.
    4. For problem_number, use the exact K-identifier (e.g., "K-1", "K-23")
    5. If a page has NO problems (e.g., title page, contents, preface), return an empty list
    6. Include any diagrams descriptions, definitions, or context that are part of the problem
    7. Capture everything until the next problem starts or the page ends
    8. Some problems have multiple parts - include all parts in problem_text
    
    EXAMPLES OF VALID KLEE PROBLEMS:
    - problem_number: "K-1"
      problem_text: "Does every finite set in E^d have a Steiner minimum tree?"
      answer: null
    
    - problem_number: "K-5"
      problem_text: "Given a finite set S in the plane, does there exist a connected graph G with vertex set S such that (a) G has minimum total edge length among all connected graphs with vertex set S, and (b) G has no cycle?"
      answer: null
    
    - problem_number: "K-12"
      problem_text: "Let P be a convex polygon in the plane. Can P always be partitioned into a minimum number of convex parts using only cuts along diagonals of P?"
      answer: null
    
    NOTE: Geometry problems often contain:
    - Set notation (E^d for d-dimensional Euclidean space)
    - Multiple parts labeled (a), (b), (c)
    - References to figures or diagrams
    - Technical geometric terms (convex hull, Steiner tree, etc.)
    
    Make sure to capture all of these elements in the problem_text.
    
    Page text:
    {{ page_text }}
  "#
}

function ExtractGreenProblems(page_text: string, page_number: int) -> PageProblems {
  client GPT4o
  prompt #"
    Extract all problems from this page of "100 Open Problems" by Ben Green.
    
    Page number: {{ page_number }}
    
    IMPORTANT RULES:
    1. Look for problems with "Problem N" format where N is a number (e.g., "Problem 1", "Problem 18", "Problem 43")
    2. Some problems are marked "(Solved)" - include this in the problem_text if present
    3. Extract the COMPLETE problem statement including all mathematical notation and context
    4. For problem_number, use just the number (e.g., "1", "18", "43")
    5. If a page has NO problems (e.g., references, preface), return an empty list
    6. Include "Comments" or "Update" sections that are part of the problem discussion
    7. Capture the full problem text until the next "Problem N" appears or the page ends
    8. Problems may have multiple questions or parts - include everything
    
    EXAMPLES OF VALID GREEN PROBLEMS:
    - problem_number: "1"
      problem_text: "Problem 1. (Solved) Is there a set A ⊆ {1,...,n} of size |A| = Ω(n) which does not contain three elements in arithmetic progression?..."
      answer: null
    
    - problem_number: "18"
      problem_text: "Problem 18. Suppose that G is a finite group, and let A ⊂ G × G be a subset of size |A| ≥ δ|G|²..."
      answer: null
    
    - problem_number: "43"
      problem_text: "Problem 43. Let N be a large integer. For each prime p with N^0.51 ≤ p < 2N^0.51, choose a random residue class ap (mod p)..."
      answer: null
    
    NOTE: These are research-level mathematical problems that may contain:
    - Advanced mathematical notation and symbols
    - References to theorems, papers, and mathematicians
    - Update sections with recent progress
    - Multiple sub-questions or variants
    - Technical definitions and background
    
    Make sure to capture the full context and all mathematical details.
    
    Page text:
    {{ page_text }}
    
    {{ ctx.output_format }}
  "#
}

function FixGAPCode(
  original_code: string,
  error_message: string,
  previous_attempts: string[]
) -> GAPCodeFix {
  client GPT4o
  prompt #"
    You are an expert GAP programmer debugging failing code.

    {{ _.role("system") }}

    # GAP SYNTAX REFERENCE (abbreviated)

    ## Common Mistakes
    - Missing semicolons
    - Wrong function names (e.g., `Center` vs `Centre`)
    - Incorrect argument types
    - Using undefined variables
    - Missing package loads (e.g., SmallGroups needs `LoadPackage("SmallGrp")`)
    - Wrong operator precedence
    - Using expressions in statement context

    ## Debugging Tips
    - Check capitalization: `IsAbelian` not `isAbelian`
    - GAP uses `Centre` not `Center` (but accepts both)
    - List indices start at 1, not 0
    - `<>` means "not equal", not `!=`
    - `and`/`or` not `&&`/`||`
    - Ranges: `[1..10]` not `range(1,10)`

    {{ _.role("user") }}

    The following GAP code failed:
    ```gap
    {{ original_code }}
    ```

    Error message:
    ```
    {{ error_message }}
    ```

    {% if previous_attempts|length > 0 %}
    Previous failed attempts (DO NOT repeat these):
    {% for attempt in previous_attempts %}
    Attempt {{ loop.index }}: {{ attempt }}
    {% endfor %}
    {% endif %}

    Fix the code. Provide corrected GAP code and explain what was wrong.

    {{ ctx.output_format }}
  "#
}

// Function to extract math problems from Kourovka Notebook

function ExtractKourovkaProblems(page_text: string, page_number: int) -> PageProblems {
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