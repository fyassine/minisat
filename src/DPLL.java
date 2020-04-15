import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.*;

/**
 * This class is represents the dpll algorithm solving cnf clauses
 *
 * @author Fraj Yassine Lakhal <fyassine.lakhal@tum.de>
 * @version 0.9 (Beta Release)
 */

public class DPLL {
    private final String filePath;
    /**
     * The following map links the original variable that appears in expression
     * to its encoded value
     **/
    private HashMap<String, Integer> originalAndEncodedVars = new HashMap<>();

    /**
     * Represents the current clauses along the way
     * meaning it will be modified when variables get removed
     */
    private HashSet<HashSet<Integer>> currentClauses = new HashSet<>();

    private HashSet<HashSet<Integer>> savedClauses = new HashSet<>();

    /**
     * Stores the literal and its setting
     */
    private HashMap<String, Boolean> settings = new HashMap<>();

    /**
     * A list of all the given variables in expression in order of appearance
     */
    private List<String> orderedVariables;

    /**
     * The outcome of the algorithm
     * true: means the expression is satisfiable
     * false: means the opposite
     */
    public boolean sat = false;

    /**
     * Tells if the algorithm is still working on the expression
     */
    private boolean stillWorking = true;


    public static void main(String[] args) {
        new DPLL().startSolvingProcess();
    }

    /**
     * The constructor of the current class
     * cnf file given must respect a general form
     * - literals can be of any character type
     * - there must be between every literal a single space
     * - clauses must end with " 0" to be distinguished
     * example = "F -A B D # A V -F 0"
     */

    public DPLL() {
        filePath = "example.cnf";
    }

    /**
     * The following method starts the solving process and finishes it
     * All contained methods represent a separate step in the dpll algorithm
     */
    public void startSolvingProcess() {
        parseEntry();

        orderedVariables = new ArrayList<>(originalAndEncodedVars.keySet());

        // TODO remove
        //System.out.println("Original Expression after formatting:");
        //System.out.println(currentClausesToString());

        deepCopySet(currentClauses, savedClauses);

        dpllSolver();

        if (sat) {
            stillWorking = false;
            System.out.println(printSettings());
            System.out.println("expression is satisfiable.");
        } else {
            System.out.println("expression is not satisfiable.");
        }
    }


    /**
     * This method parses the expression given
     * It updates the currentClauses accordingly
     */
    private void parseEntry() {
        try {
            Files.lines(Paths.get(filePath)).forEach(clause -> {
                HashSet<Integer> encodedClause = new HashSet<>();

                int negated;
                int encodedVariable;

                String literalsJoined = clause.substring(0, clause.indexOf(" 0"));
                for (String literal : literalsJoined.split(" ")) {
                    negated = literal.startsWith("-") ? 1 : 0;
                    String originalVariable = literal.substring(negated);

                    encodedVariable = originalAndEncodedVars.keySet().size() << 1;

                    if (!originalAndEncodedVars.containsKey(originalVariable)) {
                        // the position of the literal in the set is the encoding method
                        originalAndEncodedVars.put(originalVariable, encodedVariable);
                    } else {
                        encodedVariable = originalAndEncodedVars.get(originalVariable);
                    }
                    encodedClause.add(encodedVariable | negated);
                }
                currentClauses.add(encodedClause);
            });
        } catch (IOException e) {
            e.printStackTrace();
        }

    }

    /**
     * Checks if the encoded variable corresponds to the original one
     * Prints the setting of variable given
     * Stores the setting in the settings map
     *
     * @param encodedVariable  is the variable given transformed into a number
     * @param originalVariable is the variable given in expression
     */
    private void setVariable(Integer encodedVariable, String originalVariable) {
        boolean setting = encodedVariable.equals(originalAndEncodedVars.get(originalVariable));

        settings.put(originalVariable, setting);
        // TODO remove if not needed
        //System.out.println(originalVariable + " is set to: " + setting);
    }

    /**
     * Searches for a unit clause
     *
     * @return the first unit variable that appears in the clauses
     */
    private Optional<Integer> getUnitVariable() {
        return currentClauses
                .stream()
                .filter((clause) -> clause.size() == 1)
                .map(AbstractCollection::toArray)
                .map((clause) -> (Integer) clause[0])
                .findFirst();
    }


    /**
     * ++OLR++
     * Short for: One Literal Rule
     * The method proceeds as follows:
     * If a unit variable is found it will be given in the console
     * And the currentClauses will be updated
     * ++PLR++
     * Short for: Plural Literal Rule
     * The method acts almost like the olrProcess method
     * with the exception that no unit variable is needed
     * variables will be picked by order appearance
     * and processed with the same logic as in the olr part
     **/

    private int index = 0;
    private int backtrackingInt = 1;
    HashSet<String> unitVariables = new HashSet<>();

    private void dpllSolver() {
        // while there is clauses to process
        // first round (set all variables)
        while (stillWorking && !sat) {
            String originalVariable;

            // Working on unit variables
            Optional<Integer> possibleUnitVariable = getUnitVariable();
            if (possibleUnitVariable.isPresent()) {
                Integer unitVariableEncoded = possibleUnitVariable.get();
                originalVariable = findAssociatedOriginalVariable(unitVariableEncoded);
                // TODO remove if not needed
                //System.out.println("Found a unit variable: " + originalVariable);

                setVariable(unitVariableEncoded, originalVariable);
                processClauses(unitVariableEncoded);
                // TODO remove if not needed
                //System.out.println(currentClausesToString());

                Collections.swap(orderedVariables, index, orderedVariables.indexOf(originalVariable));
                unitVariables.add(originalVariable);

                // expression is not satisfiable with current settings
                if (!checkSAT()) {
                    settings.remove(orderedVariables.get(index));
                    index -= backtrackingInt++;

                    // the unitVariables list contains all the unit variable
                    // the orderedVariables list however every variable but
                    // with unit variables in the front
                    // means arriving at the first unit variable while backtracking is the end of the algorithm

                    if (index == -1 || unitVariables.contains(orderedVariables.get(index))) {
                        stillWorking = false;
                    } else {
                        // currentClauses must be updated after resetting the last variable
                        deepCopySet(savedClauses, currentClauses);
                        for (int i = 0; i < index; i++) {
                            processClauses(originalAndEncodedVars.get(orderedVariables.get(i)));
                        }
                        // TODO remove if not needed
                        //System.out.println("------RESET(last resort)------\n" + currentClausesToString());
                        index--;
                    }
                }

            } else {
                originalVariable = orderedVariables.get(index);
                Integer setEncodedVariableDefault = originalAndEncodedVars.get(originalVariable);

                // look if the variable is contained in the clauses
                Integer finalSetEncodedVariable = setEncodedVariableDefault;
                Optional<HashSet<Integer>> clausesContainingVariable = currentClauses.stream().filter((clause) -> clause.contains(finalSetEncodedVariable) ||
                        clause.contains(finalSetEncodedVariable ^ 1)).findAny();
                boolean variableAppearsInClauses = clausesContainingVariable.isPresent();

                if (variableAppearsInClauses) {

                    // choose between negated or no negated variable depending on clauses
                    boolean variableAppearsNegated = currentClauses.stream().allMatch((clause) -> clause.contains(finalSetEncodedVariable ^ 1));
                    // set the chosen variable to the one appearing in the clause
                    if (variableAppearsNegated) {
                        setEncodedVariableDefault = setEncodedVariableDefault ^ 1;
                    }

                    // the removing of the variable in the clauses and further checking
                    // the variable is already set
                    // we try the opposite setting
                    if (settings.containsKey(originalVariable)) {
                        setEncodedVariableDefault = setEncodedVariableDefault ^ 1;
                    }

                    setVariable(setEncodedVariableDefault, originalVariable);
                    processClauses(setEncodedVariableDefault);
                    // TODO remove if not needed
                    //System.out.println(currentClausesToString());
                }
            }
            // we advance in the list to the next variable
            index++;

            // check if satisfiable
            checkSAT();
        }
    }

    /**
     * @return returns
     * false: only when a the expression is not satisfiable
     * true: in every other case
     */
    private boolean checkSAT() {
        boolean stillSatisfiable = true;
        if (currentClauses.isEmpty()) {
            sat = true;
        } else if (currentClauses.stream().allMatch(HashSet::isEmpty)) {
            stillSatisfiable = false;
        }
        return stillSatisfiable;
    }


    /*
     * A whole clause will be removed if it contains the variable
     * Only the variable will be removed if it's negated
     */
    private void processClauses(Integer encodedVariable) {

        // remove clauses containing the variable
        currentClauses.removeIf(clause -> clause.contains(encodedVariable) || clause.isEmpty());
        // remove the negated variable from the other clauses
        int negatedVariable = encodedVariable ^ 1;
        for (HashSet<Integer> clause : currentClauses) {
            clause.removeIf(variable -> variable == negatedVariable);
        }

    }


    /**
     * @param encodedVariable is the variable given transformed into a number
     * @return the decoded variable (given in expression)
     */
    private String findAssociatedOriginalVariable(Integer encodedVariable) {
        Optional<String> associatedOriginalVariable = originalAndEncodedVars
                .keySet()
                .stream()
                .filter((entry) -> Objects.equals(encodedVariable, originalAndEncodedVars.get(entry)) ||
                        Objects.equals(encodedVariable, originalAndEncodedVars.get(entry) ^ 1))
                .findFirst();

        associatedOriginalVariable.orElseThrow(() ->
                new NoSuchElementException("The given variable is not included in the original variables."));

        return associatedOriginalVariable.get();
    }


    /**
     * Method used to check the currentClauses
     *
     * @return prints the current status of the clauses
     * (the current cnf clauses in a certain format)
     */
    private String currentClausesToString() {
        StringBuilder output = new StringBuilder();
        for (HashSet<Integer> currentClause : currentClauses) {
            StringBuilder clause = new StringBuilder();
            for (Integer encodedVariable : currentClause) {
                /* two cases emerge:
                 * 1- the variable is negated (not pair)
                 * 2- the variable is not negated (pair)
                 */
                StringBuilder associatedOriginalVariable = new StringBuilder();
                if (Integer.lowestOneBit(encodedVariable) == 1) {
                    encodedVariable -= 1;
                    associatedOriginalVariable.append("-");
                }
                associatedOriginalVariable.append(findAssociatedOriginalVariable(encodedVariable));
                clause.append(associatedOriginalVariable).append(" ");
            }
            output.append(clause).append("# \n");
        }
        return output.toString();
    }


    /**
     * @return a string with the original and the encoded variable side by side
     */
    private String originalVariablesToEncoded() {
        StringBuilder output = new StringBuilder();
        for (String original : originalAndEncodedVars.keySet()) {
            output.append("Original: ").append(original).append(" --->");
            output.append(" Encoded to: ").append(originalAndEncodedVars.get(original)).append("  \n");
        }
        return output.toString();
    }


    /**
     * @return a string with all the variables and their settings
     */
    public String printSettings() {
        StringBuilder output = new StringBuilder();
        for (String originalVariable : settings.keySet()) {
            output.append("Variable: ").append(originalVariable);
            output.append(" is set to: ").append(settings.get(originalVariable)).append("  \n");
        }
        return output.toString();
    }

    private void deepCopySet(HashSet<HashSet<Integer>> original, HashSet<HashSet<Integer>> clone) {
        clone.clear();
        for (HashSet<Integer> set : original) {
            clone.add((HashSet<Integer>) set.clone());
        }
    }

    public HashMap<String, Boolean> getSettings() {
        return settings;
    }
}