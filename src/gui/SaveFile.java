package gui;

import java.io.Serializable;
import java.util.Vector;

import Expression.Expr;
import Symbolic.Var;
import code.Program;
import code.Programs;

public class SaveFile implements Serializable
{
    Program[] programs;
    String[] source_code;
    Vector<String> input;
    Vector<Expr> output;
    Vector<Var> vars;
    Vector<Expr> values;
    String parser_io;
    
    
    public SaveFile(Program[] prg, String[] code, Vector<String> in, Vector<Expr> out, Vector<Var> v, Vector<Expr> vals, String pio)
    {
    	programs = prg;
    	source_code = code;
    	input = in;
    	output = out;
    	vars = v;
    	values = vals;
    	parser_io = pio;
    }
    
    public static SaveFile getSaveFile()
    {
    	return new SaveFile(Programs.prgms, Programs.src_code, InOut.input, InOut.output, InOut.variables, InOut.values, Main.textArea.getText());
    }

	public static void open(SaveFile sf)
	{
		Programs.prgms = sf.programs;
		Main.list.setListData(Programs.prgms);
		Programs.src_code = sf.source_code;
	    InOut.input = sf.input;
	    InOut.output = sf.output;
	    InOut.variables = sf.vars;
	    InOut.values = sf.values;
	    Main.textArea.setText(sf.parser_io);
	}
    
}
