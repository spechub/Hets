$(document).ready(function() {
  $('.ui.accordion').accordion();

  $('.ui.checkbox').checkbox();

  $('.ui.dropdown').dropdown({
    allowCategorySelection: true
  });

  $('.ui.file.input').find('input:text, .ui.button').on('click', function(event) {
      $(event.target).parent().find('input:file').click();
  });

  $('input:file', '.ui.file.input').on('change', function(event) {
      var file = $(event.target);
      var name = '';

      for (var i = 0; i < event.target.files.length; i++) {
        name += event.target.files[i].name + ', ';
      }
      // remove trailing ","
      name = name.replace(/,\s*$/, '');

      $('input:text', file.parent()).val(name);
  });

  $('.insert-example-into-user-input-text').on('click', function(event) {
    // Insert text into textarea
    var text = $(event.target).attr('data-text');
    $('#user-input-text').text(text);

    // Select the input-type
    var inputType = $(event.target).attr('data-input-type');
    $('#user-file-input-type').val(inputType);
  });
})
