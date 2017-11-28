$(document).ready(function() {
  $('.ui.file.input').find('input:text, .ui.button').on('click', function(e) {
      $(e.target).parent().find('input:file').click();
  });

  $('input:file', '.ui.file.input').on('change', function(e) {
      var file = $(e.target);
      var name = '';

      for (var i=0; i<e.target.files.length; i++) {
        name += e.target.files[i].name + ', ';
      }
      // remove trailing ","
      name = name.replace(/,\s*$/, '');

      $('input:text', file.parent()).val(name);
  });

  $('.ui.dropdown').dropdown();

  $('.ui.accordion').accordion();
})
