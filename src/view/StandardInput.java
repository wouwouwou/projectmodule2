package view;

import java.util.Scanner;

/**
 * Support class for other classes.
 * 
 * @author Jan-Jaap van Raffe and Wouter Bos
 * @version v1.0
 */
public class StandardInput {

	/*@ requires prompt != null && !prompt.equals("") &&
		yes != null && !yes.equals("") && no != null && !no.equals("");
	*/
	/**
	 * Prints a question which can be answered by yes (true) or no (false).
	 * After prompting the question on standard out, this method reads a String
	 * from standard in and compares it to the parameters for yes and no. If the
	 * user inputs a different value, the prompt is repeated and the method
	 * reads input again.
	 * 
	 * @param prompt
	 *            the question to print
	 * 
	 * @param yes
	 *            the String corresponding to a yes answer
	 * 
	 * @param no
	 *            the String corresponding to a no answer
	 * 
	 * @return true is the yes answer is typed, false if the no answer is typed
	 */
	public static boolean readBoolean(String prompt, String yes, String no) {
		String answer;
		Scanner in;
		do {
			System.out.print(prompt);
			in = new Scanner(System.in);
			answer = in.hasNextLine() ? in.nextLine() : null;
		} while (answer == null || (!answer.equals(yes) && !answer.equals(no)));
		in.close();
		return answer.equals(yes);
	}
	
	/*@ requires prompt != null && !prompt.equals("") &&
		option1 != null && !option1.equals("") && option2 != null && !option2.equals("");
	 */
	/**
	 * Prints a question which can be answered with two options. After prompting
	 * the question on standard out, this method reads a String from standard in
	 * and compares it to the parameters for the two options. If the user inputs
	 * a different value, the prompt is repeated and the method reads input
	 * again.
	 * 
	 * @param prompt
	 *            the question to print
	 * 
	 * @param option1
	 *            the String corresponding to the first option
	 * 
	 * @param option2
	 *            the String corresponding to the second option
	 * 
	 * @return the option typed.
	 */
	public static String readChoice(String prompt, String option1,
				 String option2) {
		String answer;
		Scanner in;
		do {
			System.out.print(prompt);
			in = new Scanner(System.in);
			answer = in.hasNextLine() ? in.nextLine() : null;
		} while (answer == null
				|| (!answer.equals(option1) && !answer.equals(option2)));
		in.close();
		return answer;
	}

	/**
	 * Writes a prompt to standard out and tries to read an int value from
	 * standard in. This is repeated until an int value is entered.
	 * 
	 * @param prompt
	 *            the question to prompt the user
	 * @return the first int value which is entered by the user
	 */
	public static int readInt(String prompt) {
		int value = 0;
		boolean intRead = false;
		Scanner in;
		Scanner scannerline;
		do {
			System.out.print(prompt);
			in = new Scanner(System.in);
			String line = in.nextLine();
			scannerline = new Scanner(line);
			if (scannerline.hasNextInt()) {
				intRead = true;
				value = scannerline.nextInt();
			}
		} while (!intRead);
		in.close();
		scannerline.close();
		return value;
	}
	
	/*@ requires prompt != null && !prompt.equals("");
	 	ensures !\result.equals("") && \result != null;
	 */
	/**
	 * Prints a question which can be answered with a String. After prompting
	 * the question on standard out, this method reads a String from standard in
	 * and gives it back to the caller.
	 * 
	 * @param prompt
	 *            the question to print.
	 * 
	 * @return the string typed.
	 */
	public static String getString(String prompt) {
		String res;
		Scanner in;
		do {
			System.out.print(prompt);
			in = new Scanner(System.in);
			res = in.hasNextLine() ? in.nextLine() : null;
		} while (res.equals("") || res == null);
		in.close();
		return res;
	}

}
