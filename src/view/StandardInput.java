package view;

import java.util.Scanner;

/**
 * Support class for other view classes.
 * 
 * @author Jan-Jaap van Raffe and Wouter Bos
 * @version v1.0
 *
 */

public class StandardInput {
	
	/**
     * Prints a question which can be answered by yes (true) or no (false).
     * After prompting the question on standard out, this method reads a String
     * from standard in and compares it to the parameters for yes and no. If the
     * user inputs a different value, the prompt is repeated and the method reads
     * input again.
     * 
     * @param prompt the question to print
     * 
     * @param yes
     * the String corresponding to a yes answer
     *            
     * @param no
     * the String corresponding to a no answer
     *            
     * @return true is the yes answer is typed, false if the no answer is typed
     */
    public static boolean readBoolean(String prompt, String yes, String no) {
        String answer;
        do {
            System.out.print(prompt);
            Scanner in = new Scanner(System.in);
            answer = in.hasNextLine() ? in.nextLine() : null;
        } while (answer == null || (!answer.equals(yes) && !answer.equals(no)));
        return answer.equals(yes);
    }
    
    /**
     * Prints a question which can be answered with two options.
     * After prompting the question on standard out, this method reads a String
     * from standard in and compares it to the parameters for the two options. If the
     * user inputs a different value, the prompt is repeated and the method reads
     * input again.
     * 
     * @param prompt 
     * the question to print
     * 
     * @param option1
     * the String corresponding to the first option
     * 
     * @param option2
     * the String corresponding to the second option
     * 
     * @return the option typed.
     */
    public static String readChoice(String prompt, String option1, String option2) {
        String answer;
        do {
            System.out.print(prompt);
            Scanner in = new Scanner(System.in);
            answer = in.hasNextLine() ? in.nextLine() : null;
        } while (answer == null || (!answer.equals(option1) && !answer.equals(option2)));
        return answer;
    }
    
    /**
     * Prints a question which can be answered with a String.
     * After prompting the question on standard out, this method reads a String
     * from standard in and gives it back to the caller.
     * 
     * @param prompt
     * the question to print.
     * 
     * @return the string typed.
     */
    public static boolean readServerShutdown() {
    	String res;
    	do {
			System.out.print("Type EXIT to shut the server down");
			Scanner in = new Scanner(System.in);
    		res = in.hasNextLine() ? in.nextLine() : null;
		} while (!res.equals("EXIT"));
    	return true;
    }
    
    /**
     * Prints a question which can be answered with a String.
     * After prompting the question on standard out, this method reads a String
     * from standard in and gives it back to the caller.
     * 
     * @param prompt
     * the question to print.
     * 
     * @return the string typed.
     */
    public static String getString(String prompt) {
    	String res;
    	do {
			System.out.print(prompt);
			Scanner in = new Scanner(System.in);
    		res = in.hasNextLine() ? in.nextLine() : null;
		} while (res.equals(""));
    	return res;
    }
	
}
