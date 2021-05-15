var wanted_tab = 0;

function change_tab(file_id, index) {
    if (index > 2 || index < 0 || isNaN(index)) {
        throw new Error('No tab with such index exists');
    }

    wanted_tab = index;

    const tab_buttons = document.getElementById('tabs')
                                .getElementsByTagName('ul')[0]
                                .getElementsByTagName('li');

    const tab_window = document.getElementById("tab-data");

    const xhttp = new XMLHttpRequest();
    xhttp.onreadystatechange = function() {
        if (this.readyState == XMLHttpRequest.DONE && this.status == 200) {
            if (wanted_tab != index) return;

            let parser = get_parser();
            const resp = parser.parseFromString(this.responseText, "text/html");
            replace(resp, 'bottom');
        }
        else if (this.readyState == XMLHttpRequest.OPENED) {
            for (let i = 0; i < tab_buttons.length; ++i) {
                if (i == index) {
                    tab_buttons[i].className = 'active';
                }
                else {
                    tab_buttons[i].className = '';
                }
            }
            tab_window.innerHTML = get_spinner();
        }
    }

    xhttp.open("GET", "/noframa/" + file_id + "?tab=" + index, true);
    xhttp.send();
}