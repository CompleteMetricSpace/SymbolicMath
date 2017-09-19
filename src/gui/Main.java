package gui;

import javax.swing.JFrame;

import java.awt.CardLayout;
import java.awt.GridBagLayout;
import java.awt.GridLayout;

import javax.swing.JFileChooser;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTabbedPane;

import java.awt.GridBagConstraints;

import javax.swing.JTextArea;
import javax.swing.JTextField;

import java.awt.Insets;

import javax.swing.JButton;
import javax.swing.JList;

import Expression.Expr;
import Expression.Parser;
import Simplification.Simplification;
import code.Program;
import code.Programs;

import java.awt.Font;
import java.awt.event.ActionListener;
import java.awt.event.ActionEvent;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;

import javax.swing.JMenuBar;

import java.awt.BorderLayout;

import javax.swing.JMenu;
import javax.swing.JMenuItem;
import javax.swing.JSeparator;

import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.io.File;
import java.io.FileFilter;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;

import javax.swing.ScrollPaneConstants;
import javax.swing.filechooser.FileNameExtensionFilter;
import javax.swing.text.DefaultCaret;
import javax.swing.UIManager;
import javax.swing.AbstractAction;
import javax.swing.Action;

public class Main extends JFrame
{
    public static JTextField textField;
    public static JList list;
    private JButton compute_button;
    public static JTextArea textArea;
    public static Compute cmp = new Compute();
    public static final JScrollPane scrollPane = new JScrollPane();
    public static JTextArea textArea_program_io;
    public static String text_program_io = "";
    public static String text_parser_io = "";
    public static boolean file_changed = false;
    public static File save_file;
    public static FileNameExtensionFilter file_filter_sc = new FileNameExtensionFilter("SC-Files", "sc");

    public Main()
    {
	getContentPane().setLayout(new GridLayout(1, 1));

	JPanel panel = new JPanel();
	getContentPane().add(panel);
	panel.setLayout(new BorderLayout(0, 0));
	JTabbedPane tp = new JTabbedPane();
	panel.add(tp, BorderLayout.CENTER);

	JPanel parser_panel = new JPanel();
	tp.add(parser_panel, "Parser");
	GridBagLayout gbl_parser_panel = new GridBagLayout();
	gbl_parser_panel.columnWidths = new int[] {0, 0, 0};
	gbl_parser_panel.rowHeights = new int[] {0, 0, 0, 0};
	gbl_parser_panel.columnWeights = new double[] {0.0, 1.0, Double.MIN_VALUE};
	gbl_parser_panel.rowWeights = new double[] {1.0, 0.0, 0.0, Double.MIN_VALUE};
	parser_panel.setLayout(gbl_parser_panel);

	scrollPane.setHorizontalScrollBarPolicy(ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);
	GridBagConstraints gbc_scrollPane = new GridBagConstraints();
	gbc_scrollPane.weighty = 2.0;
	gbc_scrollPane.gridwidth = 2;
	gbc_scrollPane.insets = new Insets(5, 5, 5, 5);
	gbc_scrollPane.fill = GridBagConstraints.BOTH;
	gbc_scrollPane.gridx = 0;
	gbc_scrollPane.gridy = 0;
	parser_panel.add(scrollPane, gbc_scrollPane);

	textArea = new JTextArea();
	textArea.setEditable(false);
	textArea.setFont(new Font("Courier New", Font.PLAIN, 20));
	scrollPane.setViewportView(textArea);

	textField = new JTextField();
	textField.addKeyListener(new KeyAdapter()
	{
	    @Override
	    public void keyPressed(KeyEvent e)
	    {
		if(e.getKeyCode() == 10)
		    compute_button.doClick();
	    }
	});
	textField.setFont(new Font("Courier New", Font.PLAIN, 20));
	GridBagConstraints gbc_textField = new GridBagConstraints();
	gbc_textField.weighty = 0.1;
	gbc_textField.gridwidth = 2;
	gbc_textField.insets = new Insets(0, 5, 0, 5);
	gbc_textField.fill = GridBagConstraints.BOTH;
	gbc_textField.gridx = 0;
	gbc_textField.gridy = 1;
	parser_panel.add(textField, gbc_textField);
	textField.setColumns(10);

	compute_button = new JButton("Compute");
	compute_button.addActionListener(new ActionListener()
	{
	    public void actionPerformed(ActionEvent arg0)
	    {
		String s = textField.getText();
		if(!s.isEmpty())
		{
		    file_changed = true;
		    if(cmp.isAlive())
		    {
			cmp.stop();
			textArea.setText(textArea.getText().replace("\n Computing...", ""));
			Compute c = new Compute();
			cmp = c;
			cmp.start();
		    } else
		    {
			Compute c = new Compute();
			cmp = c;
			cmp.start();
		    }
		}
	    }
	});

	GridBagConstraints gbc_compute_button = new GridBagConstraints();
	gbc_compute_button.anchor = GridBagConstraints.EAST;
	gbc_compute_button.insets = new Insets(5, 5, 5, 5);
	gbc_compute_button.gridx = 0;
	gbc_compute_button.gridy = 2;
	parser_panel.add(compute_button, gbc_compute_button);

	JButton btnCopy = new JButton("Copy");
	GridBagConstraints gbc_btnCopy = new GridBagConstraints();
	gbc_btnCopy.insets = new Insets(5, 5, 5, 5);
	gbc_btnCopy.anchor = GridBagConstraints.WEST;
	gbc_btnCopy.fill = GridBagConstraints.VERTICAL;
	gbc_btnCopy.gridx = 1;
	gbc_btnCopy.gridy = 2;
	parser_panel.add(btnCopy, gbc_btnCopy);

	JPanel program_panel = new JPanel();
	tp.add(program_panel, "Programs");
	GridBagLayout gbl_program_panel = new GridBagLayout();
	gbl_program_panel.columnWidths = new int[] {0, 0, 0};
	gbl_program_panel.rowHeights = new int[] {0, 0, 0, 0};
	gbl_program_panel.columnWeights = new double[] {1.0, 0.0, Double.MIN_VALUE};
	gbl_program_panel.rowWeights = new double[] {0.0, 0.0, 1.0, Double.MIN_VALUE};
	program_panel.setLayout(gbl_program_panel);

	list = new JList(Programs.prgms);
	list.setFont(new Font("Courier New", Font.PLAIN, 20));
	JScrollPane scroll_pane_list = new JScrollPane();
	GridBagConstraints gbc_scroll_pane_list = new GridBagConstraints();
	gbc_scroll_pane_list.gridheight = 3;
	gbc_scroll_pane_list.insets = new Insets(10, 10, 10, 10);
	gbc_scroll_pane_list.fill = GridBagConstraints.BOTH;
	gbc_scroll_pane_list.gridx = 0;
	gbc_scroll_pane_list.gridy = 0;
	program_panel.add(scroll_pane_list, gbc_scroll_pane_list);
	scroll_pane_list.setViewportView(list);

	JButton btnEdit = new JButton("Edit");
	btnEdit.addActionListener(new ActionListener()
	{
	    public void actionPerformed(ActionEvent arg0)
	    {
		int index = list.getSelectedIndex();
		if(index >= 0)
		    GUI.start((Program) list.getSelectedValue(), Programs.src_code[index], index);

	    }
	});
	GridBagConstraints gbc_btnEdit = new GridBagConstraints();
	gbc_btnEdit.anchor = GridBagConstraints.NORTH;
	gbc_btnEdit.fill = GridBagConstraints.HORIZONTAL;
	gbc_btnEdit.insets = new Insets(5, 5, 5, 5);
	gbc_btnEdit.gridx = 1;
	gbc_btnEdit.gridy = 0;
	program_panel.add(btnEdit, gbc_btnEdit);

	JButton btnAdd = new JButton("Add");
	btnAdd.addActionListener(new ActionListener()
	{
	    public void actionPerformed(ActionEvent e)
	    {
		file_changed = true;
		GUI.start(null, "", -1);
	    }
	});
	GridBagConstraints gbc_btnAdd = new GridBagConstraints();
	gbc_btnAdd.anchor = GridBagConstraints.NORTH;
	gbc_btnAdd.fill = GridBagConstraints.HORIZONTAL;
	gbc_btnAdd.insets = new Insets(5, 5, 5, 5);
	gbc_btnAdd.gridx = 1;
	gbc_btnAdd.gridy = 1;
	program_panel.add(btnAdd, gbc_btnAdd);

	JButton btnRemove = new JButton("Remove");
	GridBagConstraints gbc_btnRemove = new GridBagConstraints();
	gbc_btnRemove.insets = new Insets(5, 5, 5, 5);
	gbc_btnRemove.anchor = GridBagConstraints.NORTH;
	gbc_btnRemove.fill = GridBagConstraints.HORIZONTAL;
	gbc_btnRemove.gridx = 1;
	gbc_btnRemove.gridy = 2;
	program_panel.add(btnRemove, gbc_btnRemove);

	JPanel prgio_panel = new JPanel();
	tp.addTab("Program IO", prgio_panel);
	GridBagLayout gbl_prgio_panel = new GridBagLayout();
	gbl_prgio_panel.columnWidths = new int[] {0, 0};
	gbl_prgio_panel.rowHeights = new int[] {0, 0};
	gbl_prgio_panel.columnWeights = new double[] {1.0, Double.MIN_VALUE};
	gbl_prgio_panel.rowWeights = new double[] {1.0, Double.MIN_VALUE};
	prgio_panel.setLayout(gbl_prgio_panel);

	JScrollPane scroll_pane_io = new JScrollPane();
	GridBagConstraints gbc_scroll_pane_io = new GridBagConstraints();
	gbc_scroll_pane_io.insets = new Insets(5, 5, 5, 5);
	gbc_scroll_pane_io.fill = GridBagConstraints.BOTH;
	gbc_scroll_pane_io.gridx = 0;
	gbc_scroll_pane_io.gridy = 0;
	prgio_panel.add(scroll_pane_io, gbc_scroll_pane_io);

	textArea_program_io = new JTextArea();
	textArea_program_io.setEditable(false);
	textArea_program_io.setLineWrap(true);
	textArea_program_io.setFont(new Font("Courier New", Font.PLAIN, 20));
	scroll_pane_io.setViewportView(textArea_program_io);

	JButton clear_button = new JButton("Clear");
	GridBagConstraints gbc_clear_button = new GridBagConstraints();
	gbc_clear_button.insets = new Insets(5, 5, 5, 5);
	gbc_clear_button.anchor = GridBagConstraints.WEST;
	gbc_clear_button.gridy = 1;
	gbc_clear_button.gridx = 0;
	gbc_scroll_pane_io.fill = GridBagConstraints.BOTH;
	gbc_scroll_pane_io.gridx = 1;
	gbc_scroll_pane_io.gridy = 0;
	prgio_panel.add(clear_button, gbc_clear_button);

	JMenuBar menuBar = new JMenuBar();
	panel.add(menuBar, BorderLayout.NORTH);

	JMenu mnFile = new JMenu("File");
	menuBar.add(mnFile);

	JMenuItem mntmNew = new JMenuItem("New");
	mnFile.add(mntmNew);

	JMenuItem mntmOpen = new JMenuItem("Open");
	mnFile.add(mntmOpen);

	JSeparator separator = new JSeparator();
	mnFile.add(separator);

	final JMenuItem mntmClose = new JMenuItem("Close");
	mnFile.add(mntmClose);

	JSeparator separator_1 = new JSeparator();
	mnFile.add(separator_1);

	final JMenuItem mntmSave = new JMenuItem("Save");
	mnFile.add(mntmSave);
	final JMenuItem mntmSaveAs = new JMenuItem("Save as...");
	mnFile.add(mntmSaveAs);

	mntmNew.addActionListener(new ActionListener()
	{
	    public void actionPerformed(ActionEvent arg0)
	    {
		boolean cancel = false;
		if(file_changed)
		{
		    int n = JOptionPane.showConfirmDialog(null, "Do you want to save?", "Cancel",
			    JOptionPane.YES_NO_CANCEL_OPTION);
		    if(n == JOptionPane.YES_OPTION)
			mntmSave.doClick();
		    if(n == JOptionPane.CANCEL_OPTION)
			cancel = true;
		}
		if(!cancel)
		{
		    Programs.prgms = new Program[] {};
		    Main.list.setListData(Programs.prgms);
		    Programs.src_code = new String[] {};
		    InOut.input.clear();
		    ;
		    InOut.output.clear();
		    ;
		    InOut.variables.clear();
		    InOut.values.clear();
		    Main.textArea.setText("");
		    Main.textArea_program_io.setText("");
		}
	    }
	});

	mntmClose.addActionListener(new ActionListener()
	{
	    public void actionPerformed(ActionEvent arg0)
	    {
		boolean cancel = false;
		if(file_changed)
		{
		    int n = JOptionPane.showConfirmDialog(null, "Do you want to save?", "Confirm Exit",
			    JOptionPane.YES_NO_CANCEL_OPTION);
		    if(n == JOptionPane.YES_OPTION)
			mntmSave.doClick();
		    if(n == JOptionPane.CANCEL_OPTION)
			cancel = true;
		}
		if(!cancel)
		    System.exit(0);
	    }
	});

	mntmOpen.addActionListener(new ActionListener()
	{
	    public void actionPerformed(ActionEvent arg0)
	    {
		if(file_changed)
		{
		    int n = JOptionPane.showConfirmDialog(null, "Do you want to save?", "New File", JOptionPane.YES_NO_OPTION);
		    if(n == JOptionPane.YES_OPTION)
			mntmSave.doClick();
		}
		JFileChooser fc = new JFileChooser();
		fc.setFileFilter(file_filter_sc);
		int rg = fc.showOpenDialog(null);
		if(rg == JFileChooser.APPROVE_OPTION)
		{
		    File f = fc.getSelectedFile();
		    try
		    {
			ObjectInputStream objis = new ObjectInputStream(new FileInputStream(f));
			SaveFile sf = (SaveFile) objis.readObject();
			SaveFile.open(sf);
			file_changed = false;
			save_file = f;
		    } catch(IOException e)
		    {
			e.printStackTrace();
		    } catch(ClassNotFoundException e)
		    {
			e.printStackTrace();
		    }

		}
	    }
	});

	mntmSave.addActionListener(new ActionListener()
	{
	    public void actionPerformed(ActionEvent arg0)
	    {
		if(save_file == null)
		    mntmSaveAs.doClick();
		else
		{
		    File f = save_file;
		    if(!f.getPath().toLowerCase().endsWith(".sc"))
		    {
			f = new File(f.getPath() + ".sc");
		    }
		    SaveFile sf = SaveFile.getSaveFile();
		    try
		    {
			ObjectOutputStream objos = new ObjectOutputStream(new FileOutputStream(f));
			objos.writeObject(sf);
			objos.close();
			file_changed = false;
			save_file = f;
		    } catch(IOException e)
		    {
			e.printStackTrace();
		    }
		}
	    }
	});

	mntmSaveAs.addActionListener(new ActionListener()
	{
	    public void actionPerformed(ActionEvent arg0)
	    {
		JFileChooser fc = new JFileChooser();
		fc.setFileFilter(file_filter_sc);
		int rg = fc.showSaveDialog(null);
		if(rg == JFileChooser.APPROVE_OPTION)
		{
		    File f = fc.getSelectedFile();
		    if(!f.getPath().toLowerCase().endsWith(".sc"))
		    {
			f = new File(f.getPath() + ".sc");
		    }
		    SaveFile sf = SaveFile.getSaveFile();
		    try
		    {
			ObjectOutputStream objos = new ObjectOutputStream(new FileOutputStream(f));
			objos.writeObject(sf);
			objos.close();
			file_changed = false;
		    } catch(IOException e)
		    {
			e.printStackTrace();
		    }

		}
	    }
	});

	addWindowListener(new WindowAdapter()
	{
	    @Override
	    public void windowClosing(WindowEvent arg0)
	    {
		mntmClose.doClick();
	    }
	});

    }

    public static void main(String[] args)
    {
	OutMain out = new OutMain();
	InOut.out = out;
	Main m = new Main();
	m.setVisible(true);
	m.setDefaultCloseOperation(DO_NOTHING_ON_CLOSE);
	m.setSize(1000, 700);
	
    }

    public static class OutMain implements InOut.Out
    {
	@Override
	public void program_output(String s)
	{
	    Main.text_program_io += "\n >> " + s;
	    Main.textArea_program_io.setText(Main.text_program_io);
	    Main.textArea_program_io.setCaretPosition(Main.textArea_program_io.getDocument().getLength());
	}

	@Override
	public void parser_output(String s)
	{
	    if(!Main.text_parser_io.isEmpty())
		Main.text_parser_io = Main.text_parser_io + "\n  > " + s;
	    else
		Main.text_parser_io = " > " + s;
	}
    }

}
