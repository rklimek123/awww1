Object.size = function(obj) {
  var size = 0,
    key;
  for (key in obj) {
    if (obj.hasOwnProperty(key)) size++;
  }
  return size;
};

var previousContent = {};
var isCollapsed = {};

var line_rgx = /Goal [^\n]* line ([1-9][0-9]*)\)/;

function getLineNumber(str) {
    results = str.match(line_rgx);
    return results[1];
}

function collapse() {
    let me = event.currentTarget;
    let me_id = me.id;

    var collapsed = false;
    if (me_id in isCollapsed) {
        collapsed = isCollapsed[me_id];
    }
    collapsed = !collapsed;
    isCollapsed[me_id] = collapsed;

    if (!(me_id in previousContent)) {
        previousContent[me_id] = me.innerHTML;
    }

    line = getLineNumber(previousContent[me_id]);

    if (collapsed)
        me.innerHTML = "↓ Line: " + line + " ↓";
    else
        me.innerHTML = previousContent[me_id];
}
