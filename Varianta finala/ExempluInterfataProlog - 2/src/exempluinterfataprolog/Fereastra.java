/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package exempluinterfataprolog;

import java.awt.BorderLayout;
import java.awt.Component;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.awt.image.BufferedImage;
import java.io.BufferedReader;
import java.io.DataInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PipedOutputStream;
import java.io.PrintStream;
import java.util.logging.Level;
import java.util.logging.Logger;
import javax.imageio.ImageIO;
import javax.swing.ImageIcon;
import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JTextArea;

/**
 *
 * @author Irina
 */
public class Fereastra extends javax.swing.JFrame {

    /**
     * Creates new form Fereastra
     * @param titlu
     */
    ConexiuneProlog conexiune;
    Intrebare_intrebatoare panou_intrebari;
    public Fereastra(String titlu) {
        super(titlu);
        panou_intrebari=new Intrebare_intrebatoare();
        initComponents();

    }

    /**
     * This method is called from within the constructor to initialize the form.
     * WARNING: Do NOT modify this code. The content of this method is always
     * regenerated by the Form Editor.
     */
    @SuppressWarnings("unchecked")
    // <editor-fold defaultstate="collapsed" desc="Generated Code">//GEN-BEGIN:initComponents
    private void initComponents() {

        grupBtn = new javax.swing.ButtonGroup();
        jScrollPane1 = new javax.swing.JScrollPane();
        textAreaDebug = new javax.swing.JTextArea();
        b_incarca = new javax.swing.JButton();
        b_consulta = new javax.swing.JButton();
        tfFisier = new javax.swing.JTextField();
        imagine = new javax.swing.JLabel();
        tfFisierInput = new javax.swing.JTextField();
        b_incarca_input = new javax.swing.JButton();
        tfFisierNume = new javax.swing.JTextField();
        b_trimite = new javax.swing.JButton();
        tfFisierPrenume = new javax.swing.JTextField();

        setDefaultCloseOperation(javax.swing.WindowConstants.EXIT_ON_CLOSE);
        setBackground(new java.awt.Color(40, 168, 179));
        setCursor(new java.awt.Cursor(java.awt.Cursor.DEFAULT_CURSOR));
        setMinimumSize(new java.awt.Dimension(523, 700));
        getContentPane().setLayout(new org.netbeans.lib.awtextra.AbsoluteLayout());

        textAreaDebug.setColumns(20);
        textAreaDebug.setFont(new java.awt.Font("Comic Sans MS", 1, 13)); // NOI18N
        textAreaDebug.setRows(5);
        textAreaDebug.setBorder(new javax.swing.border.LineBorder(new java.awt.Color(40, 168, 179), 5, true));
        jScrollPane1.setViewportView(textAreaDebug);

        getContentPane().add(jScrollPane1, new org.netbeans.lib.awtextra.AbsoluteConstraints(81, 520, 370, -1));

        b_incarca.setBackground(new java.awt.Color(40, 168, 179));
        b_incarca.setFont(new java.awt.Font("Tahoma", 1, 13)); // NOI18N
        b_incarca.setText("Incarca regulile");
        b_incarca.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                b_incarcaActionPerformed(evt);
            }
        });
        getContentPane().add(b_incarca, new org.netbeans.lib.awtextra.AbsoluteConstraints(40, 90, -1, -1));

        b_consulta.setBackground(new java.awt.Color(40, 168, 179));
        b_consulta.setFont(new java.awt.Font("Tahoma", 1, 13)); // NOI18N
        b_consulta.setText("Afla diagnostic");
        b_consulta.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                b_consultaActionPerformed(evt);
            }
        });
        getContentPane().add(b_consulta, new org.netbeans.lib.awtextra.AbsoluteConstraints(200, 480, -1, -1));

        tfFisier.setHorizontalAlignment(javax.swing.JTextField.CENTER);
        tfFisier.setText("'reguli.txt'");
        tfFisier.setBorder(new javax.swing.border.LineBorder(new java.awt.Color(40, 168, 179), 5, true));
        tfFisier.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                tfFisierActionPerformed(evt);
            }
        });
        getContentPane().add(tfFisier, new org.netbeans.lib.awtextra.AbsoluteConstraints(40, 60, 130, -1));

        imagine.setIcon(new javax.swing.ImageIcon(getClass().getResource("/exempluinterfataprolog/medic.png"))); // NOI18N
        getContentPane().add(imagine, new org.netbeans.lib.awtextra.AbsoluteConstraints(110, 90, 310, 363));

        tfFisierInput.setHorizontalAlignment(javax.swing.JTextField.CENTER);
        tfFisierInput.setText("'input.txt'");
        tfFisierInput.setBorder(new javax.swing.border.LineBorder(new java.awt.Color(40, 168, 179), 5, true));
        tfFisierInput.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                tfFisierInputActionPerformed(evt);
            }
        });
        getContentPane().add(tfFisierInput, new org.netbeans.lib.awtextra.AbsoluteConstraints(330, 60, 130, -1));

        b_incarca_input.setBackground(new java.awt.Color(40, 168, 179));
        b_incarca_input.setFont(new java.awt.Font("Tahoma", 1, 13)); // NOI18N
        b_incarca_input.setText("Incarca input");
        b_incarca_input.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                b_incarca_inputActionPerformed(evt);
            }
        });
        getContentPane().add(b_incarca_input, new org.netbeans.lib.awtextra.AbsoluteConstraints(330, 90, 130, -1));

        tfFisierNume.setHorizontalAlignment(javax.swing.JTextField.CENTER);
        tfFisierNume.setText("'nume'");
        tfFisierNume.setBorder(new javax.swing.border.LineBorder(new java.awt.Color(40, 168, 179), 5, true));
        tfFisierNume.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                tfFisierNumeActionPerformed(evt);
            }
        });
        getContentPane().add(tfFisierNume, new org.netbeans.lib.awtextra.AbsoluteConstraints(210, 10, 130, -1));

        b_trimite.setBackground(new java.awt.Color(40, 168, 179));
        b_trimite.setFont(new java.awt.Font("Tahoma", 1, 13)); // NOI18N
        b_trimite.setText("Trimite");
        b_trimite.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                b_trimiteActionPerformed(evt);
            }
        });
        getContentPane().add(b_trimite, new org.netbeans.lib.awtextra.AbsoluteConstraints(380, 10, -1, -1));

        tfFisierPrenume.setHorizontalAlignment(javax.swing.JTextField.CENTER);
        tfFisierPrenume.setText("'prenume'");
        tfFisierPrenume.setBorder(new javax.swing.border.LineBorder(new java.awt.Color(40, 168, 179), 5, true));
        tfFisierPrenume.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                tfFisierPrenumeActionPerformed(evt);
            }
        });
        getContentPane().add(tfFisierPrenume, new org.netbeans.lib.awtextra.AbsoluteConstraints(70, 10, 130, -1));

        pack();
    }// </editor-fold>//GEN-END:initComponents

    private void tfFisierActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_tfFisierActionPerformed
        // TODO add your handling code here:
    }//GEN-LAST:event_tfFisierActionPerformed

    private void b_incarcaActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_b_incarcaActionPerformed
        Fereastra.AFISAT_SOLUTII=false;
        String valoareParametru=tfFisier.getText();
        tfFisier.setEnabled(false);
        String dir=System.getProperty("user.dir");
        dir=dir.replace("\\", "/");
        try {
            conexiune.expeditor.trimiteMesajSicstus("director('"+dir+"')");
            conexiune.expeditor.trimiteMesajSicstus("incarca("+valoareParametru+")");
            
        
        } catch (InterruptedException ex) {
            Logger.getLogger(Fereastra.class.getName()).log(Level.SEVERE, null, ex);
        }
        
    }//GEN-LAST:event_b_incarcaActionPerformed
                                 
    
    private void b_consultaActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_b_consultaActionPerformed
       
        this.remove(this.b_incarca);
        this.remove(this.b_incarca_input);
        this.remove(this.b_consulta);
        this.remove(this.tfFisier);
        this.remove(this.tfFisierInput);
        this.remove(this.b_trimite);
        this.remove(this.tfFisierNume);
        this.remove(this.tfFisierPrenume);
        
        this.setLayout(new FlowLayout());
        this.add(this.panou_intrebari);
        this.panou_intrebari.paint(null);
        this.panou_intrebari.revalidate();
        this.repaint();
        this.revalidate();
        try {
            conexiune.expeditor.trimiteMesajSicstus("comanda(consulta)");
        } catch (InterruptedException ex) {
            Logger.getLogger(Fereastra.class.getName()).log(Level.SEVERE, null, ex);
        }
    }//GEN-LAST:event_b_consultaActionPerformed

    private void tfFisierInputActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_tfFisierInputActionPerformed
        // TODO add your handling code here:
    }//GEN-LAST:event_tfFisierInputActionPerformed

    private void b_incarca_inputActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_b_incarca_inputActionPerformed
        
        Fereastra.AFISAT_SOLUTII=false;
        String valoareParametru=tfFisierInput.getText();
        tfFisierInput.setEnabled(false);
        String dir=System.getProperty("user.dir");
        dir=dir.replace("\\", "/");
        try {
            conexiune.expeditor.trimiteMesajSicstus("director('"+dir+"')");
            conexiune.expeditor.trimiteMesajSicstus("incarca_input("+valoareParametru+")");
            
        
        } catch (InterruptedException ex) {
            Logger.getLogger(Fereastra.class.getName()).log(Level.SEVERE, null, ex);
        }
        
    }//GEN-LAST:event_b_incarca_inputActionPerformed

    private void tfFisierNumeActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_tfFisierNumeActionPerformed
        // TODO add your handling code here:
    }//GEN-LAST:event_tfFisierNumeActionPerformed

    private void b_trimiteActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_b_trimiteActionPerformed
        // TODO add your handling code here:
        Fereastra.AFISAT_SOLUTII=false;
        valoareParametru1=tfFisierNume.getText();
        tfFisierNume.setEnabled(false);
        valoareParametru2=tfFisierPrenume.getText();
        tfFisierPrenume.setEnabled(false);
        String dir=System.getProperty("user.dir");
        dir=dir.replace("\\", "/");
        
        try {
            conexiune.expeditor.trimiteMesajSicstus("director('"+dir+"')");
            //conexiune.expeditor.trimiteMesajSicstus("executa_nume(" + valoareParametru1 +")");
            conexiune.expeditor.trimiteMesajSicstus("executa_nume([" + valoareParametru1 +","+ valoareParametru2 +"])");
        } catch (InterruptedException ex) {
            Logger.getLogger(Fereastra.class.getName()).log(Level.SEVERE, null, ex);
        }
        
    }//GEN-LAST:event_b_trimiteActionPerformed

    private void tfFisierPrenumeActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_tfFisierPrenumeActionPerformed
        // TODO add your handling code here:
    }//GEN-LAST:event_tfFisierPrenumeActionPerformed

    
     private void optiuneButtonActionPerformed(java.awt.event.ActionEvent evt) {                                           
       
        String raspuns= ((JButton)(evt.getSource())).getText();
        try {
            conexiune.expeditor.trimiteSirSicstus(raspuns);
        } catch (InterruptedException ex) {
            Logger.getLogger(Fereastra.class.getName()).log(Level.SEVERE, null, ex);
        }
    }  
    
    public static void main(String args[]) {

        java.awt.EventQueue.invokeLater(new Runnable() {
            public void run() {
                new Fereastra("Verificare").setVisible(true);
                
            }
        });
    }
    
    private void b_afisareActionPerformed(java.awt.event.ActionEvent evt) {                                          
        
        try {
         conexiune.expeditor.trimiteMesajSicstus("fapte");
        } catch (InterruptedException ex) {
            Logger.getLogger(Fereastra.class.getName()).log(Level.SEVERE, null, ex);
        }
    }   
    
    private void b_cumActionPerformed(String time, java.awt.event.ActionEvent evt) {   
        
        String nume = valoareParametru1.substring(1, valoareParametru1.length()-1);
        String prenume = valoareParametru2.substring(1, valoareParametru2.length()-1);
        String file="C:/Users/Talida/Desktop/ExempluInterfataProlog/ExempluInterfataProlog - 2/output_sistem_expert/utilizatori/"+ prenume +"_"+ nume + "/d" + time + ".txt";
        System.out.print("File:"+file);
        try{
                //open the file
                FileInputStream inMessage = new FileInputStream(file);
                // Get the object of DataInputStream
                DataInputStream in = new DataInputStream(inMessage);
                BufferedReader br = new BufferedReader(new InputStreamReader(in));
                String strLine;
                StringBuilder sb = new StringBuilder();
                //Read File Line By Line
                while ((strLine = br.readLine()) != null)   {
                      // Print the content on the console
                      sb.append("\n");
                      sb.append(strLine);
                }
                    //Close the input stream
                    in.close();
                    
                JFrame content = new JFrame("Cum?");
                JTextArea info_from_file = new JTextArea(sb.toString());
                info_from_file.setLineWrap(true);
                info_from_file.setWrapStyleWord(true);
                content.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
                content.getContentPane().add(info_from_file, BorderLayout.CENTER);
                content.pack();
                //content.add(info_from_file);
                content.setVisible(true);
                
        }catch (Exception e){//Catch exception if any
              System.err.println("Error: " + e.getMessage());
        }
        
                    
        
    }

    
        private void b_resetActionPerformed(java.awt.event.ActionEvent evt) {                                        

        this.remove(this.b_incarca);
        this.remove(this.b_incarca_input);
        this.remove(this.b_consulta);
        this.remove(this.b_trimite);
        this.remove(this.tfFisier);
        this.remove(this.tfFisierNume);
        this.remove(this.tfFisierPrenume);
        this.remove(this.tfFisierInput);
        this.remove(this.panou_intrebari);
        this.remove(this.textAreaDebug);
        this.remove(this.jScrollPane1);
        this.remove(this.imagine);
        this.remove(this.b_reset);
        this.remove(this.b_afisare);
        this.remove(this.b_cum);
        this.remove(this.label);
        

        this.repaint();
        this.revalidate();

        try {
            conexiune.expeditor.trimiteMesajSicstus("comanda(reset)");

        } catch (InterruptedException ex) {
            Logger.getLogger(Fereastra.class.getName()).log(Level.SEVERE, null, ex);
        }
        panou_intrebari=new Intrebare_intrebatoare();
        initComponents();
    }  

    public javax.swing.JTextArea getDebugTextArea(){
        return textAreaDebug;
    }
    
    
    public void setConexiune(ConexiuneProlog _conexiune){
        conexiune=_conexiune;
    }
    public void setIntrebare(String intreb){
        this.panou_intrebari.label_intrebare.setText("<html><body style='width:100%;'>"+intreb+"</html>");
        this.panou_intrebari.repaint();
    }
     public void setOptiuni(String optiuni){
        this.panou_intrebari.panou_optiuni.removeAll();
        this.panou_intrebari.panou_optiuni.setLayout(new FlowLayout());
        optiuni=optiuni.trim();
        optiuni=optiuni.substring(1,optiuni.length()-1);
        optiuni=optiuni.trim();
        String[] vect_opt=optiuni.split(" ");
        for(int i=0;i<vect_opt.length;i++)
        {
            JButton b=new JButton(vect_opt[i]);
            b.addActionListener(new java.awt.event.ActionListener() {
                public void actionPerformed(java.awt.event.ActionEvent evt) {
                    optiuneButtonActionPerformed(evt);
                }
            });
            this.panou_intrebari.panou_optiuni.add(b);
        }
        this.panou_intrebari.panou_optiuni.repaint();
        this.panou_intrebari.panou_optiuni.revalidate();
        //this.revalidate();
    }  
     public void setCum(final String time){
     
             b_cum.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                    b_cumActionPerformed(time, evt);
            }
        });
     }
     public void setSolutie(final String solutie){
        
         this.remove(this.imagine);
//        this.panou_intrebari.label_intrebare.setText("<html><body style='width:100%;'>"+solutie+"</html>");
//        this.panou_intrebari.repaint();

        b_reset.setBackground(new java.awt.Color(40, 168, 179));
        b_reset.setFont(new java.awt.Font("Arial", 1, 13)); // NOI18N
        b_reset.setText("Resetare");
        b_reset.setToolTipText("Resetare");
        b_reset.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                b_resetActionPerformed(evt);
            }
        });
        getContentPane().add(b_reset, new org.netbeans.lib.awtextra.AbsoluteConstraints(491, 0, 40, 30));
        
        
        b_afisare.setBackground(new java.awt.Color(40, 168, 179));
        b_afisare.setFont(new java.awt.Font("Tahoma", 1, 13)); // NOI18N
        b_afisare.setText("Afisare fapte");
        b_afisare.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                b_afisareActionPerformed(evt);
            }
        });
        getContentPane().add(b_afisare, new org.netbeans.lib.awtextra.AbsoluteConstraints(190, 50, 130, -1));

        b_cum.setBackground(new java.awt.Color(40, 168, 179));
        b_cum.setFont(new java.awt.Font("Tahoma", 1, 13)); // NOI18N
        b_cum.setText("Cum?");
        getContentPane().add(b_cum, new org.netbeans.lib.awtextra.AbsoluteConstraints(190, 50, 130, -1));
        
         if(!Fereastra.AFISAT_SOLUTII)
        {
            this.panou_intrebari.removeAll();
            this.panou_intrebari.setLayout(new FlowLayout());
            Fereastra.AFISAT_SOLUTII=true;
        }

        JTextArea jsol=new JTextArea(solutie);
        jsol.setColumns(40);
        jsol.setRows(6);
        jsol.setLineWrap(true);         
        this.panou_intrebari.add(jsol);

        this.panou_intrebari.repaint();
        this.panou_intrebari.revalidate();
        this.revalidate();
    } 
     
     public void setNoSolutie(String solutie){
        
         this.remove(this.imagine);

        b_reset.setBackground(new java.awt.Color(40, 168, 179));
        b_reset.setFont(new java.awt.Font("Arial", 1, 13)); // NOI18N
        b_reset.setText("Resetare");
        b_reset.setToolTipText("Resetare");
        b_reset.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                b_resetActionPerformed(evt);
            }
        });
        getContentPane().add(b_reset, new org.netbeans.lib.awtextra.AbsoluteConstraints(491, 0, 40, 30));
        
        
        b_afisare.setBackground(new java.awt.Color(40, 168, 179));
        b_afisare.setFont(new java.awt.Font("Tahoma", 1, 13)); // NOI18N
        b_afisare.setText("Afisare fapte");
        b_afisare.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                b_afisareActionPerformed(evt);
            }
        });
        getContentPane().add(b_afisare, new org.netbeans.lib.awtextra.AbsoluteConstraints(190, 50, 130, -1));

         if(!Fereastra.AFISAT_SOLUTII)
        {
            this.panou_intrebari.removeAll();
            this.panou_intrebari.setLayout(new FlowLayout());
            Fereastra.AFISAT_SOLUTII=true;
        }

        JTextArea jsol=new JTextArea(solutie);
        jsol.setColumns(40);
        jsol.setRows(6);
        jsol.setLineWrap(true);         
        this.panou_intrebari.add(jsol);

        this.panou_intrebari.repaint();
        this.panou_intrebari.revalidate();
        this.revalidate();
    } 
     
     public void afiseaza_imagine(String path) {
         
            ImageIcon image = new ImageIcon(path);
            label = new JLabel("", image, JLabel.CENTER);
            this.add( label, BorderLayout.CENTER );
     }
    
    
    public static boolean AFISAT_SOLUTII=false;
    JLabel label;
    JButton b_reset=new JButton();
    JButton b_afisare=new JButton();
    JButton b_cum=new JButton();
    
    String valoareParametru1;
    String valoareParametru2;
    
    
    // Variables declaration - do not modify//GEN-BEGIN:variables
    private javax.swing.JButton b_consulta;
    private javax.swing.JButton b_incarca;
    private javax.swing.JButton b_incarca_input;
    private javax.swing.JButton b_trimite;
    private javax.swing.ButtonGroup grupBtn;
    private javax.swing.JLabel imagine;
    private javax.swing.JScrollPane jScrollPane1;
    private javax.swing.JTextArea textAreaDebug;
    private javax.swing.JTextField tfFisier;
    private javax.swing.JTextField tfFisierInput;
    private javax.swing.JTextField tfFisierNume;
    private javax.swing.JTextField tfFisierPrenume;
    // End of variables declaration//GEN-END:variables
}