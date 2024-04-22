$(document).ready(function () {
  const username = "mgwiki";
  const repo = "mgw_test";
  const apiUrl = `https://api.github.com/repos/${username}/${repo}/docs/contents`;

  $.ajax({
    url: apiUrl,
    dataType: "json",
    success: function (data) {
      data.forEach(function (item) {
        let listItem = $("<li></li>");
        let itemLink = $("<a></a>");

        if (item.type === "file") {
          itemLink.attr("href", item.download_url);
          itemLink.text(item.name);
        } else if (item.type === "dir") {
          itemLink.attr("href", item.html_url);
          itemLink.text(item.name + "/");
        }

        listItem.append(itemLink);
        $("#directory-list").append(listItem);
      });
    },
    error: function (error) {
      console.error("Error fetching directory contents:", error);
    },
  });
});
