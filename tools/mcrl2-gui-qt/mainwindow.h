// Author(s): Rimco Boudewijns
// Copyright: see the accompanying file COPYING or copy at
// https://svn.win.tue.nl/trac/MCRL2/browser/trunk/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//

/**

  @file mainwindow.h
  @author R. Boudewijns

  Main Window of mCRL2-gui used as GUI

*/

#ifndef MCRL2_GUI_MAINWINDOW_H
#define MCRL2_GUI_MAINWINDOW_H

#include <QMainWindow>
#include <QFileDialog>

#include "ui_mainwindow.h"
#include "toolcatalog.h"
#include "toolinformation.h"

class MainWindow : public QMainWindow
{
    Q_OBJECT
  public:
    /**
     * @brief Constructor
     * @param parent The parent QWidget for the window
     */
    MainWindow(QWidget *parent = 0);

    /**
     * @brief Destructor
     */
    ~MainWindow();

    /**
     * @brief Initialises the File Browser
     */
    void initFileBrowser();

    /**
     * @brief Creates the tool menu
     */
    void createToolMenu();

  public slots:

    /**
     * @brief Updates the statusbar with the latest log output
     */
    void onLogOutput(QString level, QString hint, QDateTime timestamp, QString message, QString formattedMessage);

    /**
     * @brief Displays information about the selected tool
     */
    void onToolInfo();

  private:
    Ui::MainWindow m_ui;                      ///< The user interface generated by Qt
    ToolCatalog m_catalog;                    ///< The loaded tool_catalog.xml

};

#endif // MCRL2_GUI_MAINWINDOW_H
