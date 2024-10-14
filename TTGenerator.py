import sys # Provides access to system-specific parameters and functions.
import re # Supports the evaluation of statements with regular expressions, accommodating multiple spaces.
import os # Offers a way to interact with the operating system, such as file handling.

connectives = ["~", "^", "v", "->", "<->"] # Define logical connectives for our logical expressions.
vars = ["p", "q", "r", "T", "F"] # Set of propositions and constant values which takes the place of vars when checking or computing.
matchingBrackets = {"(": ")"} # Mapping of opening and closing brackets for validation.
precedence = {"~": 3, "^": 2, "v": 2, "->": 1, "<->": 0}  # Precedence of operators ~ being highest, <-> being lowest.

# Sets for handling bracket matching and validation.
openBrackets = set(matchingBrackets.keys())
closeBrackets = set(matchingBrackets.values())

# Lists to hold variables for later evaluation.
firstVar = []
secondVar = []
thirdVar = []

# Lists to manage negated variables.
negationFirstVar = [] 
negationSecondVar = [] 
negationThirdVar= []

variables = []

rowCount = 0
valid = True # Global flag to indicate overall statement validity.

# Flags to indicate whether specific variables are negated.
negateP = False 
negateQ = False
negateR = False

def statementFromFile():
    try:
        file = open("input.txt", "rt") # Attempt to open the specified input file.
        lines = file.readlines() # Read all lines from the file.
        logStatementCount = 0
        statement = []

        if os.path.getsize("input.txt") == 0: # os.path.getsize gets the size of the input.txt file. Prompts the user for a statement if empty, otherwise writes input to the file.
            file = open("input.txt", "w")
            print("Text File is currently empty.")
            file = open("input.txt", "w")
            file.write(input("Enter statement to store in the text file: ").lower())
            file.close()
            return statementFromFile()

        for line in lines: # It will check the content in the text file and ignore any extra spaces, ensuring that the statement is still read even if it's surrounded by spaces.
            strippedLine = line.strip() 
            if strippedLine != "":
                statement.append(strippedLine)
                logStatementCount += 1

        if logStatementCount < 2: # If there is only one statement in the text file, it will return the statement in lowercase.
            statementToReturn = statement[0]
            return statementToReturn.lower() # Return it in lowercase for consistency.
        else:
            raise ValueError(f"We found {logStatementCount} statements, input only 1 statement.") # If there are more than one statement in the text file, it will raise an error.

    except ValueError as Ve: # Every value error will be caught here.
        print(f"Invalid number of inputs: {Ve}")
        sys.exit()

    except FileNotFoundError: # If the file is not found, it will prompt the user to choose from the following options: 1. Make a new file 2. Provide input via console 3. End program.
        print("File was not found.")
        print("Please choose from the following:")
        print("1. Make a new file\n2. Provide input via console\n3. End program")

        while True:
            try:
                inputChoice = input("Enter choice: ") # Prompt for user choice.

                if inputChoice == "1": 
                    file = open("input.txt", "w") # Create a new file.
                    if os.path.getsize("input.txt") == 0:
                        file.write(input("Enter a statement: ").lower()) # Store the user’s statement.
                        file.close()
                        return statementFromFile() # Recursion so that the program will read the newly entered statement

                elif inputChoice == "2":
                    statement = input("Enter a statement: ").lower() # Directly read input from the console.
                    return statement

                elif inputChoice == "3":
                    sys.exit() # Exit the program if the user chooses this option.

                else:
                    raise ValueError("Invalid Input") # If the user enters an invalid input, it will raise an error.
                    
            except ValueError as Ve:
                print(f"Error found: {Ve}") 
                

def injectParentheses(subStatement):
    
    output = [] # Stack for building the parenthesized expression.
    operators = [] # Stack to hold operators and manage their precedence.
    tokens = subStatement.split() # Tokenize the input statement for processing.

    # Helper function to manage operator application based on precedence.
    def applyOperator():
        op = operators.pop() # Pop the last operator.
        if op == "~":
            operand = output.pop() # Pop the operand for unary negation.
            if operators: # To not cause an error when we check the top of the stack.
                if operators[-1] == "~": # Cleans output by not adding space after the operand when we do more than one negation.
                    output.append(f" {op} {operand}") # Without this ~ ~ ~ ~ q will be " ~ ~ ~ ~ q    "
                else:
                    output.append(f" {op} {operand} ")
            else:
                output.append(f" {op} {operand} ")
        else: # For binary operators
            right = output.pop()
            left = output.pop()
            output.append(f"( {left} {op} {right} )") # Rebuild the expression with parentheses.

    # Process each token in the logical statement.
    for token in tokens:
        if token in vars: # If it is a valid proposition, add it to the output.
            output.append(token)
        elif token == "~": 
            operators.append(token) # Push '~' to operator stack.
        elif token in ["^", "v", "->", "<->"]:
            while (operators and operators[-1] in connectives and # Adds to operator stack if empty or has lower precedence than top most operator.
                   precedence[operators[-1]] >= precedence[token]): # If the previous operator has higher or equal precedence than current operator, operate it
                applyOperator()
            operators.append(token) # Push the current operator to the stack.
        elif token == "(":
            operators.append(token) # Push opening bracket to the stack.
        elif token == ")":  
            while operators and operators[-1] != "(": # Follows precedence between ( and ), and brackets them.
                applyOperator() 
            operators.pop()

    # Handle any remaining operators in the stack.
    while operators:
        applyOperator()

    # The final expression with injected parentheses will be at the top of the output stack.
    return output[0] if output else ""
        
def userInput():
    global variables
    subStatements = [] # List to hold sub-statements extracted from the main statement.
    statement = statementFromFile() # Fetch the logical statement from a File.
    statement = statement.replace("t", "T").replace("f", "F")
    words = statement.split() # Split the statement into individual tokens.
    statement = re.sub(r'\s+', ' ', statement) # Trims multiple statements for clarity using regex.
    
    # Ensure the syntax is correct and parentheses are balanced.
    if syntaxChecker(words) and checkParentheses(words):
        variables, subStatements = extractPropositions(statement) # Extract unique variables and sub-statements.

        print("Propositional Variables:", variables)
        print("Sub-statements:", subStatements) # Display the extracted components for clarity.

        evaluateStatement(subStatements, variables) # Initiate evaluation of the statement.

def checkParentheses(words):
    global valid # Flag to track the overall validity of the statement.
    stackParentheses = [] # Stack for tracking opening parentheses.
    for word in words: 
        if word in matchingBrackets.keys(): # If the word is an opening bracket.
            stackParentheses.append(word) # Add to the stack.
        elif word in matchingBrackets.values(): # If it’s a closing bracket.
            if stackParentheses and matchingBrackets[stackParentheses[-1]] == word:  
                stackParentheses.pop()  
            else:
                print("Invalid Statement: Unmatched closing parenthesis") 
                valid = False # Mark statement as invalid if brackets do not match.
                return False # Return false for unbalanced parentheses.

    if not stackParentheses:  
        pass
    else:
        print("Invalid Statement: Parantheis are not balanced")
        valid = False

    if valid:
        return True # If balanced, return true.
    else:
        return False

def syntaxChecker(words):
    global valid, negateP, negateQ, negateR # Flag to track the overall validity of the statement.
    variables = [] # Store variables used, this excludes T or F.
    connectivesUsed = [] # Store connectives used.

    for index, word in enumerate(words): # Validates the syntax, checks variables and connectives.
        
        if word.isalpha() and word in vars:
            if word.islower(): #islower() filters T or F and non constant variables.
             variables.append(word)
             
        elif word in connectives: 
            connectivesUsed.append(word)
            if word == "~" and words[index + 1] in vars: # If the next element of a negation is a variable.
                i = 1
                while words[index - i] == "~": # Counts negations.
                    i += 1
                if i % 2 == 1: # Display it's negation if odd amount of negations.
                    if words[index + 1] == "p":
                        negateP = True
                    elif words[index + 1] == "q":
                        negateQ = True
                    elif words[index + 1] == "r":
                            negateR = True
                
        elif word in matchingBrackets.keys() or word in matchingBrackets.values():
            if word in matchingBrackets.keys():
                if words[index + 1] in connectives and words[index + 1] != "~":
                    print("Invalid Statement: Connective cannot follow an Open Parenthesis.") # This solves issues like ( p ( ^ q )).
                    valid = False
                    return
                if words[index + 1] in matchingBrackets.values():
                    print("Invalid Statement: Parentheses cannot be empty.") # Handles empty parentheses like ( ( ) ( p ^ q ) ).
                    valid = False
                    return
            if word in matchingBrackets.values():
                if words[index - 1] in connectives:
                    print("Invalid Statement: Closed Parenthesis cannot be preceeded by a connective.") # This solves issues like ( p ^ ) q 
                    valid = False
                    return
        elif word[0] == "~" and len(word) > 1: 
             print("Invalid Statement: Negations should be separated with a space. Maybe try ~ " + " ".join(word[1:].upper()) + "?") # Guides the user to our program's syntax.
             valid = False
             return
        elif word[0] == "(" and len(word) > 1: 
             print("Invalid Statement: Parenthesis should be separated with a space. Maybe try \"( " + " ".join(word[1:].upper())  + " ...\"?") # Guides the user to our program's syntax.
             valid = False
             return
        elif word[-1] == ")" and len(word) > 1: 
             print("Invalid Statement: Parenthesis should be separated with a space. Maybe try \"... " + " ".join(word[:-1].upper())+ " )\"?") # Guides the user to our program's syntax.
             valid = False
             return
        elif word.isalpha() and len(word) == 1:
            print("Invalid Statement: As much as we want to accept \"" + word + "\" Please enter P, Q or R as statements only. ") # Guides the user to our program's syntax.
            valid = False
            return
        else:
            print("Invalid Statement: Invalid syntax detected. " + word + " not recgonized")
            valid = False
           
            return
        
    wordList = [word for word in words if word not in matchingBrackets.keys() and word not in matchingBrackets.values()]
    # Copy of the list of words.
    # This makes sure checking of adjacent variables and connectives will go smoothly.
    # Like in p -> q ( r -> r ) where q and r are adjacent.
    # This allows ( ( ) ^ q ) and ( ( q ) q ) to be checked properly.
    # Only removes from the copy.
    # Also allows instances like ( ) to be marked as invalid.

    # Handles "( )" and other empty inputs.
    if len(wordList) == 0:
        print("Invalid Statement: no variables or connectives detected")
        valid = False
        return
    
    # Handles input that is just one connective.
    if len(wordList) == 1 and wordList[0] in connectives:
        print("Invalid Statement: cannot evaluate a connective by itself")
        valid = False
        return

    # To check syntax for adjacent variables and connectives .
    for word1, word2 in zip(wordList, wordList[1:]):
        if word1 in vars and word2 in vars:
            print("Invalid Statement: Two variables cannot be adjacent.") # Handles inputs like " p p ^ p ".
            valid = False
            return
        if word1 in vars and word2 == "~":
            print("Invalid Statement: Negation cannot proceed a variable.") # Handles inputs like " ~ p ~ q ".
            valid = False
            return
        if word1 in connectives and word2 in connectives and word2 != "~":
            print("Invalid Statement: Two connectives cannot be adjacent.") # Handles inputs like " p ^ v p".
            valid = False
            return
        if wordList[-1] in connectives:
            print("Invalid Statement: The last word cannot be a connective.") # Handles inputs like " p ^ ".
            valid = False
            return
        if wordList[0] in connectives and wordList[0] != "~":
            print("Invalid Statement: The first word cannot be a connective.") # Handles inputs like " ^ p".
            valid = False
            return

    if valid:
        uniqueVars = set(variables) # Remove duplicates from vars. Ensure we have unique variables for evaluation.
        varPopulator(len(uniqueVars), uniqueVars) # Populate variables for evaluation.
        return True
        
def varPopulator(n, uniqueVars):
    global rowCount 
    rowCount = 2 ** n # Calculate the total number of rows in the truth table, which is 2^n.
    if rowCount == 0:
        rowCount = 1 # Ensure at least one row exists for the truth table.

    if n == 3: # Populate the variables for a truth table with three variables (firstVar, secondVar, thirdVar).
        for i in range(rowCount):
            # This creates a pattern where the first variable is True for the first half of every group of four rows.
            firstVar.append("True" if (i // 4) % 2 == 0 else "False") 
            # This results in the second variable alternating every two rows, covering all combinations.
            secondVar.append("True" if (i // 2) % 2 == 0 else "False")
            # This alternates the truth value for the third variable for each row, ensuring all combinations are represented.
            thirdVar.append("True" if i % 2 == 0 else "False")      

    elif n == 2:
        for i in range(rowCount):
            firstVar.append("True" if (i // 2) % 2 == 0 else "False") 
            secondVar.append("True" if (i % 2) == 0 else "False") 

    elif n == 1: # Prepare for cases with a single variable, allowing for negation (e.g., p and not p)
        for i in range(rowCount):
            firstVar.append("True" if (i % 2) == 0 else "False")  
    calculateNegations(uniqueVars) # Passes unique vars again to negations after populating.

def calculateNegations(uniqueVars):
    global negationFirstVar, negationSecondVar, negationThirdVar
    # If P is negated, create a list of the opposite values of P (True becomes False and vice versa) same for Q and R.
    
    if rowCount == 8:
        # Every possible proposition is present and follows this order.
        negationFirstVar = ["False" if temp == "True" else "True" for temp in firstVar] if negateP else []
        negationSecondVar = ["False" if temp == "True" else "True" for temp in secondVar] if negateQ else []
        negationThirdVar = ["False" if temp == "True" else "True" for temp in thirdVar] if negateR else []
        
    elif rowCount == 4: 
        if "r" in uniqueVars: 
            # First var guarantees that either exclusively P or Q if r is present, R being always the second var.
            negationFirstVar = ["False" if temp == "True" else "True" for temp in firstVar] if negateP or negateQ else [] 
            negationSecondVar = ["False" if temp == "True" else "True" for temp in secondVar] if negateR else []
        else: #if r is not present we know variables are P and Q
            negationFirstVar = ["False" if temp == "True" else "True" for temp in firstVar] if negateP else [] 
            negationSecondVar = ["False" if temp == "True" else "True" for temp in secondVar] if negateR else []
            
    elif rowCount == 2: # If any negation is present, it's the negated first var.
         negationFirstVar = ["False" if temp == "True" else "True" for temp in firstVar] if negateP or negateQ or negateR else [] 

def removeParentheses(subst):
    # This ensures we remove unnecessary parentheses that may be wrapping the expression.
    while subst.startswith("(") and subst.endswith(")"):
        subst = subst[1:-1].strip() # Remove the outer parentheses.
    # Return the subst enclosed in parentheses if it's not empty,
    return f"( {subst} )" if subst else "" # Return an empty string if subst is empty.

def extractPropositions(statement):

    statement = injectParentheses(statement) # Ensure that the precedence of logical operators is maintained by injecting necessary parentheses.
    normalizedStatement = removeParentheses(statement) # Sorts issues like ( ( ( p v q ) ) ) causing redundant calculations.

    print(normalizedStatement)

    propositions = set()
    subStatements = []
    stackOpenBracket = []
    negateSubStatement = False
    checkNegatedCompound = False
    processedStatements = set()

    for index, char in enumerate(statement):
        
        if checkNegatedCompound: # if Negation or ~ was detected, check for next element if it's parenthesis.
            if statement[index] == " ":
                continue
            elif statement[index] == "(": # If a parenthesis follows the negation, mark that the next sub-statement needs to be negated, like ~ ( P v Q )
                negateSubStatement = True
                checkNegatedCompound = False
            else:
                checkNegatedCompound = False # If no parenthesis is found, it’s a simple negati, like ~p.
        
        if char == "~":
            i = 1
            count = 1
            # Backtrack through consecutive negations (~) to count how many there are.
            while statement[index - i] == "~" or statement[index - i] == " ":
                if statement[index - i] == "~":
                    count += 1
                i += 1
            # Only consider odd numbers of negations since ~~ cancels out. Trim extra negations for clarity.
            if count % 2 == 1: 
                 checkNegatedCompound = True 

        # Collect propositions (lowercase alphabet) while excluding logical operators like 'v' (or). 
        if char.isalpha() and char != 'v' and char.islower():
            propositions.add(char)

        if char in openBrackets:
            # If it's an open parenthesis, the parenthesis and its index will be placed in the stack, like in the case of ( p v r ) v q.
            stackOpenBracket.append((index, negateSubStatement)) 
            negateSubStatement = False # This tracks and resets negation status to be retrieved when we reach the end of the statement.
            # This fix errors later on that would happen with ~ ( p ^ ( q v r )) if this statements were not added.
                                        
        elif char in closeBrackets and stackOpenBracket:
            # When a closing parenthesis is found, extract the sub-statement from the stack's corresponding opening parenthesis.
            start, wasNegated = stackOpenBracket.pop() # Retrieve the negation state at this level
            subst = statement[start : index + 1]

            # Normalize the sub-statement by removing unnecessary outer parentheses.
            normalizedSubst = removeParentheses(subst)

            if normalizedSubst not in processedStatements:
                subStatements.append(normalizedSubst) 
                processedStatements.add(normalizedSubst) # Avoid duplicate sub-statements.

                # If the sub-statement was preceded by a negation, append the negated version.
                if wasNegated:
                    negatedSubst = "~ " + normalizedSubst
                    if negatedSubst not in processedStatements and negatedSubst != statement:
                        subStatements.append(negatedSubst)
                        processedStatements.add(negatedSubst)
                    negateSubStatement = False # Reset negation state after use.
    
    # Ensure the normalized full statement is included as a sub-statement if not already processed.
    if normalizedStatement not in processedStatements or normalizedStatement not in subStatements:
        subStatements.append(statement) 
    return sorted(propositions), subStatements # Sorted so that the propositions are returned as a list.

def evaluateStatement(subStatements, variables):
    results = [[] for _ in subStatements] # Creates empty list for the results of every subStatements.

    for i in range(rowCount):
        # When there are 3 variables, assign the corresponding values from truth table rows.
        if rowCount == 8:
            rowValues = {variables[0]: firstVar[i], variables[1]: secondVar[i], variables[2]: thirdVar[i]}  
        # When there are 2 variables, assign the corresponding values from truth table rows.
        elif rowCount == 4:
            rowValues= {variables[0]: firstVar[i], variables[1]: secondVar[i]}
        # When there is 1 variable, assign the corresponding value from truth table rows.
        elif rowCount == 2:
            rowValues = {variables[0]: firstVar[i]}
        # When there are no variables and only truth constants (T/F) are used.   
        else:
            rowValues = {}

        for index, subStatement in enumerate(subStatements):
            evaluatedResult = evalProposition(subStatement, rowValues) 
            results[index].append(evaluatedResult)

    printFinalTable(results, subStatements, variables) # Print the completed truth table with results.

def evalProposition(subStatement, rowValues):

    try:
        
        if 'r' in rowValues:
            subStatement = subStatement.replace("r", rowValues['r'])
            # Key r will be evaluated first and will be replaced by corresponding value.
            # If otherwise, p and q which truth values happen to be True will have it's r be replaced with r's value.
            # Leading to errors such as TTrueue and TFalseue

        # Replace 'p' and 'q' with their corresponding truth values from the truth table row.  
        if 'p' in rowValues:
            subStatement = subStatement.replace("p", rowValues['p'])
        
        if 'q' in rowValues:
            subStatement = subStatement.replace("q", rowValues['q'])
        
        # Replace standalone 'T' and 'F' with 'True' and 'False' respectively.
        subStatement = re.sub(r"\bT\b", "True", subStatement)
        subStatement = re.sub(r"\bF\b", "False", subStatement) 

        
        subStatement = re.sub(r'~\s*\(([^)]+)\)', r'(not (\1))', subStatement) # This is converted before simple negations.
        # This regex assures that not followed by a compound statement.
        # Is converted to ( not ( statement ) ) fixing possible issues with implication using <= instead of not p or q.
        
        subStatement = subStatement.replace("~", " not ") # Replace the simple negation symbol '~' with Python's 'not' keyword. 
        subStatement = subStatement.replace("^", " and ") # Same for other operators.
        subStatement = subStatement.replace("v", " or ")     
        subStatement = subStatement.replace("<->", " is ")   
        subStatement = subStatement.replace("->", " <= ") 

        subStatement = re.sub(r"not\s+True", "False", subStatement) # Implication has issues with -> ~ since True <= not True.
        subStatement = re.sub(r"not\s+False", "True", subStatement) # Or vice versa cant be calculated, this cleans up negations.

        return str(eval(subStatement))
    
    except Exception as e:
        # Return the error message if any exception occurs during evaluation.
        return f"Error: {str(e)}"


def printFinalTable(results, subStatements, variables):
    headers = []

    # Add variable headers if they exist in the provided variables.
    if 'p' in variables:
        headers.append("p")
    if 'q' in variables:
        headers.append("q")
    if 'r' in variables:
        headers.append("r")

    # Add negated variable headers if necessary.
    if negateP:
        headers.append("~p")
    if negateQ:
        headers.append("~q")
    if negateR:
        headers.append("~r")

    # Print headers for the variables and sub-statements.
    print(" ".join([f"{header:<10}" for header in headers]), end=" ")

    # Format and print sub-statement headers in a readable way.
    header = " ".join([f"{sub:<{len(sub) + 5}}" for sub in subStatements])
    print(header)

    # Print a separator line to distinguish the header from the table rows.
    totalWidth = 10 * len(headers) + len(header)
    print('-' * totalWidth)

    for i in range(rowCount):
        row = []

        # Print the truth values for variables for each row in the truth table.
        if rowCount == 8:
            print(f"{firstVar[i]:<10} {secondVar[i]:<10} {thirdVar[i]:<10}", end=" ")
        elif rowCount == 4:
            print(f"{firstVar[i]:<10} {secondVar[i]:<10}", end=" ")
        elif rowCount == 2:
            print(f"{firstVar[i]:<10}", end=" ")

        # Add negated values if they are present and print them.
        if len(negationFirstVar) > 0:
            row.append(f"{negationFirstVar[i]:<10}")
        if len(negationSecondVar) > 0:
            row.append(f"{negationSecondVar[i]:<10}")
        if len(negationThirdVar) > 0:
            row.append(f"{negationThirdVar[i]:<10}")

        print(" ".join(row), end=" ")

        # Print the evaluation results for each sub-statement in the current row.
        resultRow = " ".join([f"{results[j][i]:<{len(subStatements[j]) + 7}}" for j in range(len(subStatements))])
        print(resultRow)
        
# Entry point for user input
userInput()
