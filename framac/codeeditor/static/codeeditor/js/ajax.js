var parser = new DOMParser();
function get_parser() {
    return parser;
}

var loading_spinner = "<div class=\"lds-roller\"><div></div><div></div><div></div><div></div><div></div><div></div><div></div><div></div></div>";
function get_spinner() {
    return loading_spinner;
}

function replace(doc, section) {
    document.getElementById(section).innerHTML =
        doc.getElementById(section).innerHTML;
}

var wanted_file = 0;

function reload_page(url, file_id) {
    wanted_file = file_id;
    const no_frama_url = "/noframa" + url.substring(5);
    const xhttp = new XMLHttpRequest();
    xhttp.onreadystatechange = function() {
        if (this.readyState == XMLHttpRequest.DONE && this.status == 200) {
            const resp = parser.parseFromString(this.responseText, "text/html");

            replace(resp, "files");
            replace(resp, "main");
            replace(resp, "menu");
            replace(resp, "bottom");

            document.getElementById("program-elements").innerHTML =
                loading_spinner;

            reload_program_elements(url, file_id);
        }
    };
    xhttp.open("GET", no_frama_url, true);
    xhttp.send();
}

function reload_program_elements(url, file_id) {
    const xhttp = new XMLHttpRequest();
    xhttp.onreadystatechange = function () {
        if (this.readyState == XMLHttpRequest.DONE && this.status == 200) {
            if (file_id != wanted_file) return;

            const resp = parser.parseFromString(this.responseText, "text/html");

            replace(resp, "program-elements");
            reset_collapse();
        }
    }

    xhttp.open("GET", url, true);
    xhttp.send();
}

function reverify(url, file_id) {
    file_id *= -1;
    wanted_file = file_id;

    const xhttp = new XMLHttpRequest();
    xhttp.onreadystatechange = function() {
        if (this.readyState == XMLHttpRequest.DONE && this.status == 200) {
            const resp = parser.parseFromString(this.responseText, "text/html");
            if (wanted_file != file_id) return;
            replace(resp,"program-elements");
            reset_collapse();
        }
        if (this.readyState == XMLHttpRequest.OPENED) {
            document.getElementById("program-elements").innerHTML =
                loading_spinner;
        }
    };
    xhttp.open("GET", url, true);
    xhttp.send();
}