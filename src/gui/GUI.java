package gui;

import javax.swing.JFrame;

import java.awt.GridBagLayout;

import javax.swing.JTextArea;

import java.awt.GridBagConstraints;

import javax.swing.JButton;

import java.awt.GridLayout;
import java.awt.Insets;
import java.awt.Font;

import javax.swing.JList;
import javax.swing.JOptionPane;
import javax.swing.JTextField;
import javax.swing.JLabel;
import javax.swing.JScrollPane;
import javax.swing.ScrollPaneLayout;

import Expression.Expr;
import Expression.Parser;
import Symbolic.Var;
import code.CodeParser;
import code.Line;
import code.Program;
import code.Programs;

import java.awt.event.ActionListener;
import java.awt.event.ActionEvent;
import java.awt.event.WindowAdapter;

public class GUI extends JFrame
{
	private JTextField name_field;
	private JTextField param_field;
	
	public Program pr;
	public String code = ""; 
	int index = -1;
	private JTextArea edit_field;
	
	public GUI(Program prg, String cd, int id) {
		
		
		pr = prg;
		code = cd;
		index = id;
		
		GridBagLayout gridBagLayout = new GridBagLayout();
		gridBagLayout.columnWidths = new int[]{0, 0, 0, 0};
		gridBagLayout.rowHeights = new int[]{0, 0, 0, 0, 0};
		gridBagLayout.columnWeights = new double[]{1.0, 0.0, 1.0, Double.MIN_VALUE};
		gridBagLayout.rowWeights = new double[]{1.0, 0.0, 0.0, 0.0, Double.MIN_VALUE};
		getContentPane().setLayout(gridBagLayout);
		
		param_field = new JTextField();
		param_field.setFont(new Font("Tahoma", Font.PLAIN, 14));
		GridBagConstraints gbc_param_field = new GridBagConstraints();
		gbc_param_field.weighty = 1.0;
		gbc_param_field.gridwidth = 2;
		gbc_param_field.insets = new Insets(5, 5, 5, 10);
		gbc_param_field.fill = GridBagConstraints.BOTH;
		gbc_param_field.gridx = 1;
		gbc_param_field.gridy = 1;
		getContentPane().add(param_field, gbc_param_field);
		param_field.setColumns(10);
		
		JButton save_button = new JButton("Save");
		save_button.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent arg0) 
			{
				code = edit_field.getText();
				try
				{
					Line[] pc = CodeParser.parse(code);
					Expr[] param = Parser.parseArgs(param_field.getText());
					Var[] v = new Var[param.length];
					for(int i = 0;i<v.length;i++)
						v[i] = (Var)param[i];
					pr = new Program(name_field.getText(), pc, v);
					if(index != -1)
					{
					    Programs.prgms[index] = pr;
					    Programs.src_code[index] = code;
					    Main.list.setListData(Programs.prgms);
					    Main.list.repaint();
					}
					else
					{
						Program[] new_p = new Program[Programs.prgms.length+1];
						String[] new_s = new String[Programs.src_code.length+1];
						for(int i = 0;i<Programs.prgms.length;i++)
						{
							new_p[i] = Programs.prgms[i];
							new_s[i] = Programs.src_code[i];
						}
						new_p[new_p.length-1] = pr;
						new_s[new_s.length-1] = code;
						Programs.src_code = new_s;
						Programs.prgms = new_p;
						Main.list.setListData(Programs.prgms);
					    Main.list.repaint();	
					}
					dispose();
					
				} catch (Exception e) 
				{
					JOptionPane.showMessageDialog(null,"There are errors in the source code",
					                    "Syntax Error", JOptionPane.ERROR_MESSAGE);
				}
			}
		});
		save_button.setFont(new Font("Tahoma", Font.PLAIN, 14));
		GridBagConstraints gbc_save_button = new GridBagConstraints();
		gbc_save_button.anchor = GridBagConstraints.EAST;
		gbc_save_button.weightx = 1.0;
		gbc_save_button.insets = new Insets(5, 5, 5, 5);
		gbc_save_button.fill = GridBagConstraints.BOTH;
		gbc_save_button.gridx = 1;
		gbc_save_button.gridy = 3;
		getContentPane().add(save_button, gbc_save_button);
		
		JButton cancel_button = new JButton("Cancel");
		cancel_button.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) 
			{
				if(!edit_field.getText().isEmpty())
				{
					int n = JOptionPane.showConfirmDialog(
							null,
							"Do you want to quit without saving?",
							"Cancel",
							JOptionPane.YES_NO_OPTION);
					if(n == JOptionPane.YES_OPTION)
						dispose();
				}
				else
					dispose();
			}
		});
		cancel_button.setFont(new Font("Tahoma", Font.PLAIN, 14));
		GridBagConstraints gbc_cancel_button = new GridBagConstraints();
		gbc_cancel_button.anchor = GridBagConstraints.EAST;
		gbc_cancel_button.insets = new Insets(5, 5, 5, 10);
		gbc_cancel_button.fill = GridBagConstraints.BOTH;
		gbc_cancel_button.gridx = 2;
		gbc_cancel_button.gridy = 3;
		getContentPane().add(cancel_button, gbc_cancel_button);
		
		name_field = new JTextField();
		name_field.setFont(new Font("Tahoma", Font.PLAIN, 14));
		GridBagConstraints gbc_name_field = new GridBagConstraints();
		gbc_name_field.gridwidth = 2;
		gbc_name_field.insets = new Insets(5, 5, 5, 10);
		gbc_name_field.fill = GridBagConstraints.BOTH;
		gbc_name_field.gridx = 1;
		gbc_name_field.gridy = 0;
		getContentPane().add(name_field, gbc_name_field);
		name_field.setColumns(10);
		
		JLabel lblNewLabel = new JLabel("Name:");
		lblNewLabel.setFont(new Font("Tahoma", Font.PLAIN, 14));
		GridBagConstraints gbc_lblNewLabel = new GridBagConstraints();
		gbc_lblNewLabel.anchor = GridBagConstraints.WEST;
		gbc_lblNewLabel.weightx = 1.0;
		gbc_lblNewLabel.insets = new Insets(5, 10, 5, 5);
		gbc_lblNewLabel.gridx = 0;
		gbc_lblNewLabel.gridy = 0;
		getContentPane().add(lblNewLabel, gbc_lblNewLabel);
		
		JLabel lblNewLabel_1 = new JLabel("Parameters:");
		lblNewLabel_1.setFont(new Font("Tahoma", Font.PLAIN, 14));
		GridBagConstraints gbc_lblNewLabel_1 = new GridBagConstraints();
		gbc_lblNewLabel_1.anchor = GridBagConstraints.WEST;
		gbc_lblNewLabel_1.weightx = 1.0;
		gbc_lblNewLabel_1.insets = new Insets(5, 10, 5, 5);
		gbc_lblNewLabel_1.gridx = 0;
		gbc_lblNewLabel_1.gridy = 1;
		getContentPane().add(lblNewLabel_1, gbc_lblNewLabel_1);
		
		edit_field = new JTextArea();
		edit_field.setFont(new Font("Courier New", Font.PLAIN, 15));
		JScrollPane scrollPane = new JScrollPane(edit_field);
		GridBagConstraints gbc_scrollPane = new GridBagConstraints();
		gbc_scrollPane.weighty = 20.0;
		gbc_scrollPane.insets = new Insets(10, 10, 10, 10);
		gbc_scrollPane.gridwidth = 3;
		gbc_scrollPane.fill = GridBagConstraints.BOTH;
		gbc_scrollPane.gridx = 0;
		gbc_scrollPane.gridy = 2;
		getContentPane().add(scrollPane, gbc_scrollPane);
	
		
		edit_field.setText(code);
		
		if(index != -1)
		{
			//Edit a program
			
			name_field.setText(pr.getName());
			String param = pr.getParameters()[0].toString();
			for(int i = 1;i<pr.getParameters().length;i++)
				param += ","+pr.getParameters()[i].toString();
			param_field.setText(param);
		}
		else
		{
			//Create new Program
		}
		
		
		addWindowListener(new WindowAdapter()
		{
		    public void windowClosing(java.awt.event.WindowEvent windowEvent) 
		    {
		    	if(!edit_field.getText().isEmpty())
		    	{
		    		int n = JOptionPane.showConfirmDialog(null, "Do you want to quit without saving?", "Close", JOptionPane.YES_NO_OPTION);
		    		if(n == JOptionPane.YES_OPTION)
		    			dispose();
		    	}
		    	else
		    		dispose();
		    }
		});
		
		
		
	}
	
	public static void start(Program prg, String code, int index)
	{
		GUI m = new GUI(prg, code, index);
		
		m.setVisible(true);
		m.setDefaultCloseOperation(DO_NOTHING_ON_CLOSE);
		m.setSize(500, 500);	
	}

	private void setIndex(int index) 
	{
		this.index = index;
		
	}

	private void setCode(String cd) 
	{
		code = cd;	
	}

	private void setProgram(Program prg) 
	{
		pr = prg;
		
	}

}
