package gui;

public class Compute extends Thread
{

	public void run()
	{
		String s = Main.textField.getText();
		Main.textField.setText("");
		String text = Main.textArea.getText();
		String tmp_text = text+"\n Computing...";
		Main.textArea.setText(tmp_text);
		String result = InOut.out(s);
		if(result.equals("~CLEAR_PARSER_IO~"))
			Main.textArea.setText("\n >> [cleared] \n");
		else
		{
			if(Main.text_parser_io.isEmpty())
				Main.textArea.setText(text+"\n In: "+s+" \n "+result+"\n");
			else
				Main.textArea.setText(text+"\n In: "+s+" \n "+Main.text_parser_io+"\n "+result+"\n");
			Main.text_parser_io = "";
			Main.textArea.setCaretPosition(Main.textArea.getDocument().getLength());
		}
	}
}
