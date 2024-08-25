---
layout: page
title: 08 - The IMP Language
---

<!-- Navigation Links -->
<nav class="post-navigation">
  <ul>
    {% if page.previous %}
      <li><a href="{{ page.previous.url }}" class="previous-post">Previous: {{ page.previous.title }}</a></li>
    {% endif %}
    {% if page.next %}
      <li><a href="{{ page.next.url }}" class="next-post">Next: {{ page.next.title }}</a></li>
    {% endif %}
  </ul>
</nav>

{% include lec_08_imp.html %}