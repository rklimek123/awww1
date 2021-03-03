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
