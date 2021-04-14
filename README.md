# Assignment 1: Mock-up of the App Interface

The goal of the assignments in this course is to create a web application in which one can write down and prove invariants for simple programs. We assume that the code will be written in C and the invariants will be encoded in an ACSL. One may view this as a simplified version of the Frama-C program.

The goal of the first assignment is to create a general view, i.e. mock-up, of the application in a web browser. The general format of the application page should follow the layout on the following picture

Web application layout (resource named layout.png)

Remember to populate the areas of the interface with some sample data. A number of examples written in ACSL can be found here (http://toccata.lri.fr/gallery/frama-c.en.html).

**Interface layout in accordance with a picture (5 points)**
 * All panes present together with example content (1 p.)
 * Comfortable screen arrangement at the resolution 1024x768 or greater for the ratio 4:3 as well as comfortable screen arrangement at the resolution  1280x720 or greater for the ratio 16:9. (1 p.)
 * Seamless rearrangement of the content when the browser window changes size. (1 p.)
 * Correct and complete HTML structure checked without warnings by at least one of the tools: htmltest, tidy, html-validate, validator@w3.org, (1 p.)
 * Clear and legible HTML code structure (1 p.)

**CSS that specifies the look of the application (5 points)**
 * Use variables to provide at least two colour versions of the page (1 p.)
 * Use media to create a version of the layout for mobile devices (1 p.)
 * Provide both human-readable and automatically compressed (e.g. with yuicompressor) style versions (1 p.)
 * Correct CSS structure checked without warnings by at least one of the tools: csslint, css-validator@w3.org, stylelint (1 p.)
 * Style (DRY, Naming, no !important, comments for non-local dependencies) (1 p.)

# Assignment 2: server side of the application (data model, page templates, link-button interface)
In this iteration of the application you have to develop data model, page templates and link-button interface to the application.

## Data model
You have to create a data model with the following entities:
 * Directory - is an entity that holds files and other directories. In addition to descriptions of relations with other entities, it has:
   * a name,
   * an optional description,
   * a creation date
   * an owner
   * an availability flag (false if the directory was deleted)
 * File - is an entity that contains a source code, the source code is divided into sections. In addition to descriptions of relations with other entities, it has:
   * a name,
   * an optional description,
   * a creation date,
   * an owner
   * an availability flag (false if the file was deleted)
 * File section - is an entity that contains a meaningful piece of code within a file or comments; some file sections may contain subsections. In addition to descriptions of relations with other entities, it has:
   * an optional name,
   * an optional description,
   * a creation date,
   * a section category,
   * a status,
   * status data
 * Section category - is an entity that defines the type of a section; category defines the way the file section is handled by the application. Possible section categories are: procedure, property, lemma, assertion, invariant, precondition, postcondition; some file sections may contain subsections.

 * Section status - is an entity that defines the status of a section; example status' are: proved, invalid, counterexample, unchecked.

 * Status data - is an entity that defines data associated with the section status, e.g. the counterexample content, the name of the solver that proved validity (e.g. Z3, CVC4 etc.).
   * a status data field
   * a user

 * User – is an entity that defines a user of the application.
   * a name
   * a login
   * a password

*All the entities have a timestamp and a validity flag. The actual model may contain more entities and each of the entities may have more properties.


**Points**
 * Entity of users - 1 point
 * Entities related to files and directories - 1 point
 * Entities related to sections - 1 point

## Link-button interface and templates

The application should display in the File selection dialog the available in the database directory structure.
The file selection dialog should be implemented as appropriate template fed with data from the database.
The application should make it possible to add a file to the database and to divide the file into sections of mentioned above categories.
This should be done by using an appropriate option in the menu bar.
The application should make it possible to add a directory to the database.
This should be done by using an appropriate option in the menu bar.
The application should make it possible to delete a file or a directory from the application (the file should not be deleted completely from the database, it should only be marked as not available).
This should be done by using an appropriate option in the menu bar and by means of an appropriate selection of the file or a directory.
The application should display in the Focus on program elements section of the screen the output of the command

`# frama-c -wp -wp-print <filename>.c`

where filename.c corresponds to the currently selected file.
The output should be parsed into ranges inbetween dashed lines, which describe verification conditions, so that line numbers visible in each of the ranges are related to parsed sections of the input file and the names of the sections should appear in tool tips when mouse is hovered over the range text.
Also status of the verification for each of the conditions (Valid, Unknown etc.) should be parsed and the content should be displayed using different decorations depending on the status (eg. on different background).
Appropriate template should be used to display this section properly.
Three tabs should be available in the bottom part of the screen.
Their content is described below.

* The first tab (titled PROVERS) should contain a list of provers available for discharging the verification conditions generated for the chosen file (at least Alt-Ergo, Z3 and CVC4). It should be possible to choose one of the provers to discharge the goals and submit the choice to the application with a button in the tab.
* The second tab (titled VCs) should make it possible to choose runtime guard verification conditions (VCs), see option -wp-rte of frama-c, and should make it possible to choose different kinds of VCs that can be specified with the option -wp-prop="...". It should be possible to submit the choice to the application with a button in the tab.
* The third tab (titled RESULT) should contain the summary of the verification process available in the file result.txt after running the command

`# frama-c -wp -wp-log="r:result.txt"  <filename>.c`

Menu should contain an option to rerun verification operation on the current file. It should be run depending on the chosen configuration of proovers and verification conditions. Example commands that can be run here are

     # frama-c -wp -wp-prover alt-ergo -wp-prop="-@invariant" <filename>.c
     
     # frama-c -wp -wp-prover alt-ergo -wp-rte  <filename>.c
          
     # frama-c -wp -wp-prover alt-ergo -wp-prop="-@invariant" -wp-rte  <filename>.c

The application should memorise the status of proving for obligations.

**Points**
 * Content of the File selection dialog - 1 point
 * Directory and file navigation, adding, deleting- 1 point
 * Parsing of the file into sections - 1 points
 * Content of the Focus on program elements - 1 point
 * Proper handling of prover choice - 1 point
 * Proper handling of verification conditions to prove - 1 point
 * Proper presentation of the proving result  - 1 point
