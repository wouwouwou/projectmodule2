package view;

public class ConnectFour {
	
	public static void main(String[] args) {
		String playmode = StandardInput.readChoice("> Do you want to play in local-mode or in multiplayer-mode? (local/multi)?", "local", "multi");
		System.out.println(playmode);
	}

}
