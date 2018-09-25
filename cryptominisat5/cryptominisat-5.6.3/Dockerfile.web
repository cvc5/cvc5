FROM ubuntu:16.04

LABEL maintainer="Mate Soos"
LABEL version="5.0"
LABEL Description="An advanced SAT solver"

ENV LOCALE en_US.UTF-8
EXPOSE 80

RUN apt-get update && \
    DEBIAN_FRONTEND=noninteractive apt-get install --no-install-recommends -y apache2 apache2-utils libapache2-mod-php php-sqlite3 && rm -rf /var/lib/apt/lists/*

# generate dygraph & get nodejs
# cd web
# ./install_web.sh

# Setup Apache
RUN mkdir -p /var/www/site
RUN chown -R www-data: /var/www/site

# Enable apache mods.
RUN a2enmod php7.0
RUN a2enmod rewrite

# Update the PHP.ini file, enable <? ?> tags and quieten logging.
RUN sed -i "s/short_open_tag = Off/short_open_tag = On/" /etc/php/7.0/apache2/php.ini
RUN sed -i "s/error_reporting = .*$/error_reporting = E_ERROR | E_WARNING | E_PARSE/" /etc/php/7.0/apache2/php.ini

# Expose apache
EXPOSE 80

# Manually set up the apache environment variables
ENV APACHE_RUN_USER www-data
ENV APACHE_RUN_GROUP www-data
ENV APACHE_LOG_DIR /var/log/apache2
ENV APACHE_LOCK_DIR /var/lock/apache2
ENV APACHE_PID_FILE /var/run/apache2.pid

# copy dirs
COPY ./web/ /var/www/site
ADD ./web/apache-config.conf /etc/apache2/sites-enabled/000-default.conf
CMD /usr/sbin/apache2ctl -D FOREGROUND

# --------------------
# HOW TO USE
# --------------------

# run normally:
# docker run --rm  -p 8080:80 -i -t cmsweb
# -> will be accessible from host on 8080

# how to debug:
# docker run --rm  -p 8080:80 -i -t cmsweb bash
# -> will drop to shell
